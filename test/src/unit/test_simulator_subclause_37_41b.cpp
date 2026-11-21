#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class TaskFuncRulesOfARun : public VpiDesignRun {
 protected:
  static bool Same(vpiHandle a, vpiHandle b) {
    return a != nullptr && b != nullptr && vpi_compare_objects(a, b) != 0;
  }

  static int KindOf(vpiHandle obj) {
    return obj == nullptr ? 0 : vpi_get(vpiType, obj);
  }

  static vpiHandle Unit() { return Named(vpiPackage, nullptr, "$unit"); }

  static vpiHandle InTop(const char* name) {
    return Named(vpiTaskFunc, By("top"), name);
  }

  static vpiHandle InPackage(const char* pkg, const char* name) {
    return Named(vpiTaskFunc, By(pkg), name);
  }

  static vpiHandle InUnit(const char* name) {
    return Named(vpiTaskFunc, Unit(), name);
  }

  static vpiHandle MethodOf(vpiHandle defn, const char* name) {
    return Named(vpiMethods, defn, name);
  }

  static int ReturnKindOf(vpiHandle tf) {
    return KindOf(vpi_handle(vpiReturn, tf));
  }
};

TEST_F(TaskFuncRulesOfARun, AnInterfaceAndAProgramDeclareTheirSubroutines) {
  Run("interface ifc; function int f(); return 1; endfunction\n"
      "  task t(); endtask endinterface\n"
      "program prg; function int g(); return 2; endfunction\n"
      "  task u(); endtask endprogram\n"
      "module top; ifc i(); prg p(); endmodule\n");
  EXPECT_EQ(NamesOf(vpiTaskFunc, By("top.i")),
            (std::vector<std::string>{"f", "t"}));
  EXPECT_EQ(NamesOf(vpiTaskFunc, By("top.p")),
            (std::vector<std::string>{"g", "u"}));
  const struct {
    const char* scope;
    const char* name;
    int type;
    const char* full_name;
  } kExpected[] = {{"top.i", "f", vpiFunction, "top.i.f"},
                   {"top.i", "t", vpiTask, "top.i.t"},
                   {"top.p", "g", vpiFunction, "top.p.g"},
                   {"top.p", "u", vpiTask, "top.p.u"}};
  for (const auto& e : kExpected) {
    vpiHandle tf = Named(vpiTaskFunc, By(e.scope), e.name);
    ASSERT_NE(tf, nullptr) << e.full_name;
    EXPECT_EQ(vpi_get(vpiType, tf), e.type) << e.full_name;
    EXPECT_STREQ(vpi_get_str(vpiFullName, tf), e.full_name);
  }
}

TEST_F(TaskFuncRulesOfARun, APackageTaskAndAPackageClassMethodAreQualified) {
  Run("package pk; task t(); endtask\n"
      "  class C; task run(); endtask\n"
      "    function int f(); return 1; endfunction endclass\n"
      "endpackage\n"
      "module top; endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiFullName, InPackage("pk", "t")), "pk::t");
  vpiHandle c = Named(vpiClassDefn, By("pk"), "C");
  ASSERT_NE(c, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, MethodOf(c, "run")), "pk::C::run");
  EXPECT_STREQ(vpi_get_str(vpiFullName, MethodOf(c, "f")), "pk::C::f");
}

TEST_F(TaskFuncRulesOfARun, OnlyAClassesSubroutinesAreMethods) {
  Run("int n = 0;\n"
      "function int uf(); return 1; endfunction\n"
      "task ut(); endtask\n"
      "package pk; function int pf(); return 1; endfunction\n"
      "  task pt(); endtask endpackage\n"
      "module top; function int mf(); return 1; endfunction\n"
      "  task mt(); endtask\n"
      "  class C; function int cf(); return 1; endfunction\n"
      "    task ct(); endtask endclass\n"
      "endmodule\n");
  const vpiHandle kOutside[] = {InUnit("uf"),          InUnit("ut"),
                                InPackage("pk", "pf"), InPackage("pk", "pt"),
                                InTop("mf"),           InTop("mt")};
  for (vpiHandle tf : kOutside) {
    ASSERT_NE(tf, nullptr);
    EXPECT_EQ(vpi_get(vpiMethod, tf), 0) << vpi_get_str(vpiFullName, tf);
  }
  vpiHandle c = Named(vpiClassDefn, By("top"), "C");
  EXPECT_EQ(vpi_get(vpiMethod, MethodOf(c, "cf")), 1);
  EXPECT_EQ(vpi_get(vpiMethod, MethodOf(c, "ct")), 1);
}

TEST_F(TaskFuncRulesOfARun, AVirtualTaskMethodIsVirtual) {
  Run("module top; virtual class C; virtual task vt(); endtask\n"
      "  task pt(); endtask\n"
      "  pure virtual task pv(); endclass endmodule\n");
  vpiHandle c = Named(vpiClassDefn, By("top"), "C");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(vpi_get(vpiVirtual, MethodOf(c, "vt")), 1);
  EXPECT_EQ(vpi_get(vpiVirtual, MethodOf(c, "pt")), 0);
  EXPECT_EQ(vpi_get(vpiVirtual, MethodOf(c, "pv")), 1);
}

TEST_F(TaskFuncRulesOfARun, AStructReturnIsAStructVar) {
  Run("int n = 0;\n"
      "typedef struct {int a;} us_t;\n"
      "function us_t uf(); us_t r; return r; endfunction\n"
      "package pk; typedef struct packed {logic [3:0] a;} ps_t;\n"
      "  function ps_t pf(); ps_t r; return r; endfunction endpackage\n"
      "module top; typedef struct {int a; int b;} ms_t;\n"
      "  function ms_t mf(); ms_t r; return r; endfunction endmodule\n");
  EXPECT_EQ(ReturnKindOf(InUnit("uf")), vpiStructVar);
  EXPECT_EQ(ReturnKindOf(InPackage("pk", "pf")), vpiStructVar);
  EXPECT_EQ(ReturnKindOf(InTop("mf")), vpiStructVar);
}

TEST_F(TaskFuncRulesOfARun, AUnionReturnIsAUnionVar) {
  Run("int n = 0;\n"
      "typedef union {int a; shortreal b;} uu_t;\n"
      "function uu_t uf(); uu_t r; return r; endfunction\n"
      "package pk; typedef union packed {logic [7:0] a; bit [7:0] b;} pu_t;\n"
      "  function pu_t pf(); pu_t r; return r; endfunction endpackage\n"
      "module top; typedef union {int a; real b;} mu_t;\n"
      "  function mu_t mf(); mu_t r; return r; endfunction endmodule\n");
  EXPECT_EQ(ReturnKindOf(InUnit("uf")), vpiUnionVar);
  EXPECT_EQ(ReturnKindOf(InPackage("pk", "pf")), vpiUnionVar);
  EXPECT_EQ(ReturnKindOf(InTop("mf")), vpiUnionVar);
}

TEST_F(TaskFuncRulesOfARun, AClassReturnIsAClassVar) {
  Run("int n = 0;\n"
      "class UK; endclass\n"
      "function UK uf(); return null; endfunction\n"
      "package pk; class PK; endclass\n"
      "  function PK pf(); return null; endfunction endpackage\n"
      "module top; class MK; endclass\n"
      "  function MK mf(); return null; endfunction endmodule\n");
  EXPECT_EQ(ReturnKindOf(InUnit("uf")), vpiClassVar);
  EXPECT_EQ(ReturnKindOf(InPackage("pk", "pf")), vpiClassVar);
  EXPECT_EQ(ReturnKindOf(InTop("mf")), vpiClassVar);
}

TEST_F(TaskFuncRulesOfARun, EveryReturnIsAVariableOfTheFunctionsName) {
  Run("module top; function real r(); return 0; endfunction\n"
      "  function shortreal sr(); return 0; endfunction\n"
      "  function realtime rt(); return 0; endfunction\n"
      "  function time tm(); return 0; endfunction\n"
      "  function string st(); return \"\"; endfunction\n"
      "  function bit bt(); return 0; endfunction\n"
      "  function byte by(); return 0; endfunction\n"
      "  function shortint si(); return 0; endfunction\n"
      "  function longint li(); return 0; endfunction\n"
      "  function integer ig(); return 0; endfunction\n"
      "  function [3:0] im(); return 0; endfunction\n"
      "  function reg rg(); return 0; endfunction\n"
      "  function chandle ch(); return null; endfunction endmodule\n");
  const struct {
    const char* name;
    int kind;
  } kExpected[] = {
      {"r", vpiRealVar},     {"sr", vpiShortRealVar}, {"rt", vpiRealVar},
      {"tm", vpiTimeVar},    {"st", vpiStringVar},    {"bt", vpiBitVar},
      {"by", vpiByteVar},    {"si", vpiShortIntVar},  {"li", vpiLongIntVar},
      {"ig", vpiIntegerVar}, {"im", vpiLogicVar},     {"rg", vpiLogicVar},
      {"ch", vpiChandleVar}};
  for (const auto& e : kExpected) {
    vpiHandle ret = vpi_handle(vpiReturn, InTop(e.name));
    ASSERT_NE(ret, nullptr) << e.name;
    EXPECT_EQ(vpi_get(vpiType, ret), e.kind) << e.name;
    EXPECT_STREQ(vpi_get_str(vpiName, ret), e.name);
  }
}

TEST_F(TaskFuncRulesOfARun, EachFunctionIsSignedAsItsReturnTypeIs) {
  Run("int n = 0;\n"
      "function int uf(); return 0; endfunction\n"
      "function bit [3:0] ug(); return 0; endfunction\n"
      "package pk; function longint pf(); return 0; endfunction\n"
      "  function logic [3:0] pg(); return 0; endfunction endpackage\n"
      "module top; typedef struct packed {logic [3:0] a;} ps_t;\n"
      "  typedef union packed {logic [3:0] a; bit [3:0] b;} uu_t;\n"
      "  typedef enum bit [2:0] {B0, B1} eb_t;\n"
      "  typedef enum int unsigned {C0, C1} eu_t;\n"
      "  typedef int ti_t;\n"
      "  function uu_t uu(); uu_t r; return r; endfunction\n"
      "  function eb_t eb(); return B0; endfunction\n"
      "  function eu_t eu(); return C0; endfunction\n"
      "  function ti_t ti(); return 0; endfunction\n"
      "  function logic [7:0] lu(); return 0; endfunction\n"
      "  function bit bu(); return 0; endfunction\n"
      "  function ps_t pu(); ps_t r; return r; endfunction\n"
      "  function int is(); return 0; endfunction\n"
      "  function byte bs(); return 0; endfunction\n"
      "  function shortint hs(); return 0; endfunction\n"
      "  function integer gs(); return 0; endfunction\n"
      "  function logic signed [3:0] ls(); return 0; endfunction\n"
      "  function bit signed [2:0] ts(); return 0; endfunction endmodule\n");
  for (vpiHandle tf :
       {InTop("lu"), InTop("bu"), InTop("pu"), InTop("uu"), InTop("eb"),
        InTop("eu"), InUnit("ug"), InPackage("pk", "pg")}) {
    ASSERT_NE(tf, nullptr);
    EXPECT_EQ(vpi_get(vpiSigned, tf), 0) << vpi_get_str(vpiFullName, tf);
  }
  for (vpiHandle tf :
       {InTop("is"), InTop("bs"), InTop("hs"), InTop("gs"), InTop("ls"),
        InTop("ts"), InTop("ti"), InUnit("uf"), InPackage("pk", "pf")}) {
    ASSERT_NE(tf, nullptr);
    EXPECT_EQ(vpi_get(vpiSigned, tf), 1) << vpi_get_str(vpiFullName, tf);
  }
}

TEST_F(TaskFuncRulesOfARun,
       DISABLED_AFunctionTakesTheSignItsReturnTypeDeclares) {
  Run("int n = 0;\n"
      "function int unsigned uf(); return 0; endfunction\n"
      "package pk; function longint unsigned pf(); return 0; endfunction\n"
      "endpackage\n"
      "module top; typedef struct packed signed {logic [3:0] a;} ss_t;\n"
      "  typedef union packed signed {logic [3:0] a; bit [3:0] b;} su_t;\n"
      "  typedef enum {A0, A1} ei_t;\n"
      "  typedef int unsigned tu_t;\n"
      "  typedef logic signed [3:0] tl_t;\n"
      "  function ss_t ss(); ss_t r; return r; endfunction\n"
      "  function su_t su(); su_t r; return r; endfunction\n"
      "  function ei_t ei(); return A0; endfunction\n"
      "  function tu_t tu(); return 0; endfunction\n"
      "  function tl_t tl(); return 0; endfunction\n"
      "  function int unsigned iu(); return 0; endfunction\n"
      "  function byte unsigned bu(); return 0; endfunction\n"
      "  function shortint unsigned hu(); return 0; endfunction\n"
      "  function longint unsigned lu(); return 0; endfunction\n"
      "  function integer unsigned gu(); return 0; endfunction endmodule\n");
  for (vpiHandle tf :
       {InTop("iu"), InTop("bu"), InTop("hu"), InTop("lu"), InTop("gu"),
        InTop("tu"), InUnit("uf"), InPackage("pk", "pf")}) {
    ASSERT_NE(tf, nullptr);
    EXPECT_EQ(vpi_get(vpiSigned, tf), 0) << vpi_get_str(vpiFullName, tf);
  }
  for (const char* name : {"ss", "su", "ei", "tl"}) {
    EXPECT_EQ(vpi_get(vpiSigned, InTop(name)), 1) << name;
  }
}

TEST_F(TaskFuncRulesOfARun, EachFunctionsSizeIsItsReturnVariablesSize) {
  Run("int n = 0;\n"
      "function bit [9:0] uf(); return 0; endfunction\n"
      "package pk; function logic [5:0] pf(); return 0; endfunction\n"
      "endpackage\n"
      "module top; typedef struct packed {logic [3:0] a; bit [2:0] b;} ps_t;\n"
      "  typedef enum bit [2:0] {A, B} e_t;\n"
      "  function byte by(); return 0; endfunction\n"
      "  function shortint si(); return 0; endfunction\n"
      "  function longint li(); return 0; endfunction\n"
      "  function bit bt(); return 0; endfunction\n"
      "  function integer ig(); return 0; endfunction\n"
      "  function ps_t ps(); ps_t r; return r; endfunction\n"
      "  function logic [2:0][3:0] pa(); return 0; endfunction\n"
      "  function e_t en(); return A; endfunction endmodule\n");
  const struct {
    vpiHandle tf;
    int size;
  } kExpected[] = {{InUnit("uf"), 10}, {InPackage("pk", "pf"), 6},
                   {InTop("by"), 8},   {InTop("si"), 16},
                   {InTop("li"), 64},  {InTop("bt"), 1},
                   {InTop("ig"), 32},  {InTop("ps"), 7},
                   {InTop("pa"), 12},  {InTop("en"), 3}};
  for (const auto& e : kExpected) {
    ASSERT_NE(e.tf, nullptr) << e.size;
    EXPECT_EQ(vpi_get(vpiSize, e.tf), e.size) << vpi_get_str(vpiName, e.tf);
    EXPECT_EQ(vpi_get(vpiSize, vpi_handle(vpiReturn, e.tf)), e.size)
        << vpi_get_str(vpiName, e.tf);
  }
}

constexpr const char* kClassMethods =
    "module top;\n"
    "  class C;\n"
    "    protected function int pf(); return 1; endfunction\n"
    "    local task lt(); endtask\n"
    "    local function int lf(); return 1; endfunction\n"
    "    task ut(); endtask\n"
    "    function int uf(); return 1; endfunction\n"
    "    static function int sf(); return 1; endfunction\n"
    "    local static task lst(); endtask\n"
    "    protected static function int psf(); return 1; endfunction\n"
    "  endclass\n"
    "  C c = new;\n"
    "endmodule\n";

struct DeclaredVisibility {
  const char* name;
  int visibility;
};

constexpr DeclaredVisibility kDeclaredVisibilities[] = {
    {"pf", vpiProtectedVis}, {"lt", vpiLocalVis},     {"lf", vpiLocalVis},
    {"ut", vpiPublicVis},    {"uf", vpiPublicVis},    {"sf", vpiPublicVis},
    {"lst", vpiLocalVis},    {"psf", vpiProtectedVis}};

TEST_F(TaskFuncRulesOfARun, EachMethodReportsItsDeclaredVisibility) {
  Run(kClassMethods);
  vpiHandle c = Named(vpiClassDefn, By("top"), "C");
  ASSERT_NE(c, nullptr);
  for (const auto& e : kDeclaredVisibilities) {
    vpiHandle m = MethodOf(c, e.name);
    ASSERT_NE(m, nullptr) << e.name;
    EXPECT_EQ(vpi_get(vpiVisibility, m), e.visibility) << e.name;
  }
}

TEST_F(TaskFuncRulesOfARun, AMethodOfAnObjectOrTypespecKeepsItsVisibility) {
  Run(kClassMethods);
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.c"));
  vpiHandle spec = vpi_handle(vpiClassTypespec, By("top.c"));
  ASSERT_NE(obj, nullptr);
  ASSERT_NE(spec, nullptr);
  for (const auto& e : kDeclaredVisibilities) {
    vpiHandle through_obj = MethodOf(obj, e.name);
    vpiHandle through_spec = MethodOf(spec, e.name);
    ASSERT_NE(through_obj, nullptr) << e.name;
    ASSERT_NE(through_spec, nullptr) << e.name;
    EXPECT_EQ(vpi_get(vpiVisibility, through_obj), e.visibility) << e.name;
    EXPECT_EQ(vpi_get(vpiVisibility, through_spec), e.visibility) << e.name;
  }
}

TEST_F(TaskFuncRulesOfARun, ASubroutineOutsideAClassIsPublic) {
  Run("package pk; function int pf(); return 1; endfunction\n"
      "  task pt(); endtask endpackage\n"
      "interface ifc; function int jf(); return 1; endfunction\n"
      "  task jt(); endtask endinterface\n"
      "program prg; function int gf(); return 1; endfunction\n"
      "  task gt(); endtask endprogram\n"
      "module top; function int mf(); return 1; endfunction\n"
      "  task mt(); endtask\n"
      "  ifc i(); prg p(); endmodule\n");
  const vpiHandle kOutside[] = {InTop("mf"),
                                InTop("mt"),
                                InPackage("pk", "pf"),
                                InPackage("pk", "pt"),
                                Named(vpiTaskFunc, By("top.i"), "jf"),
                                Named(vpiTaskFunc, By("top.i"), "jt"),
                                Named(vpiTaskFunc, By("top.p"), "gf"),
                                Named(vpiTaskFunc, By("top.p"), "gt")};
  for (vpiHandle tf : kOutside) {
    ASSERT_NE(tf, nullptr);
    EXPECT_EQ(vpi_get(vpiVisibility, tf), vpiPublicVis)
        << vpi_get_str(vpiFullName, tf);
  }
}

constexpr const char* kMethodClasses =
    "package pk; class P; function int f(); return 1; endfunction\n"
    "  task t(); endtask endclass endpackage\n"
    "module top;\n"
    "  class B; task bt(); endtask endclass\n"
    "  class D extends B; endclass\n"
    "  class C; function int f(); return 1; endfunction\n"
    "    task t(); endtask\n"
    "    extern function int e(); endclass\n"
    "  function int C::e(); return 2; endfunction\n"
    "endmodule\n";

TEST_F(TaskFuncRulesOfARun, AMethodReachesTheClassDeclaringIt) {
  Run(kMethodClasses);
  vpiHandle c = Named(vpiClassDefn, By("top"), "C");
  vpiHandle p = Named(vpiClassDefn, By("pk"), "P");
  ASSERT_NE(c, nullptr);
  ASSERT_NE(p, nullptr);
  EXPECT_TRUE(Same(vpi_handle(vpiClassDefn, MethodOf(c, "f")), c));
  EXPECT_TRUE(Same(vpi_handle(vpiClassDefn, MethodOf(c, "t")), c));
  EXPECT_TRUE(Same(vpi_handle(vpiClassDefn, MethodOf(p, "f")), p));
  EXPECT_TRUE(Same(vpi_handle(vpiClassDefn, MethodOf(p, "t")), p));
}

TEST_F(TaskFuncRulesOfARun, AnExternMethodReachesTheClassDeclaringIt) {
  Run(kMethodClasses);
  vpiHandle c = Named(vpiClassDefn, By("top"), "C");
  vpiHandle e = MethodOf(c, "e");
  ASSERT_NE(e, nullptr);
  EXPECT_TRUE(Same(vpi_handle(vpiClassDefn, e), c));
}

TEST_F(TaskFuncRulesOfARun, AnInheritedMethodReachesOnlyTheBaseClass) {
  Run(kMethodClasses);
  vpiHandle b = Named(vpiClassDefn, By("top"), "B");
  vpiHandle d = Named(vpiClassDefn, By("top"), "D");
  ASSERT_NE(b, nullptr);
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(MethodOf(d, "bt"), nullptr);
  vpiHandle bt = MethodOf(b, "bt");
  ASSERT_NE(bt, nullptr);
  EXPECT_TRUE(Same(vpi_handle(vpiClassDefn, bt), b));
  EXPECT_FALSE(Same(vpi_handle(vpiClassDefn, bt), d));
}

constexpr const char* kInterfacePortCall =
    "interface ifc; function int f(); return 1; endfunction endinterface\n"
    "module m(ifc p); int x; initial x = p.f(); endmodule\n"
    "module top; ifc i(); m u(i); endmodule\n";

TEST_F(TaskFuncRulesOfARun,
       DISABLED_AFunctionReachedThroughAnInterfacePortHasItAsParent) {
  Run(kInterfacePortCall);
  const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By("top.u"));
  ASSERT_EQ(kProcs.size(), 1U);
  vpiHandle call = vpi_handle(vpiRhs, vpi_handle(vpiStmt, kProcs[0]));
  vpiHandle f = vpi_handle(vpiFunction, call);
  ASSERT_NE(f, nullptr);
  vpiHandle parent = vpi_handle(vpiParent, f);
  ASSERT_NE(parent, nullptr);
  EXPECT_EQ(vpi_get(vpiType, parent), vpiRefObj);
  EXPECT_STREQ(vpi_get_str(vpiName, parent), "p");
  EXPECT_TRUE(Same(vpi_handle(vpiActual, parent), By("top.i")));
}

TEST_F(TaskFuncRulesOfARun, AFunctionReachedDirectlyHasNoRefObjParent) {
  Run(kInterfacePortCall);
  vpiHandle f = Named(vpiTaskFunc, By("top.i"), "f");
  ASSERT_NE(f, nullptr);
  EXPECT_NE(KindOf(vpi_handle(vpiParent, f)), vpiRefObj);
}

constexpr const char* kDpiForms =
    "package p; import \"DPI-C\" function int p_f(); endpackage\n"
    "module top;\n"
    "  import \"DPI\" task d_t();\n"
    "  import \"DPI-C\" task i_t();\n"
    "  import \"DPI-C\" c_it = task n_t();\n"
    "  import \"DPI-C\" context task c_t();\n"
    "  import \"DPI-C\" function int i_f();\n"
    "  import \"DPI-C\" pure function int q_f();\n"
    "  task e_t(); endtask\n"
    "  export \"DPI-C\" task e_t;\n"
    "  task x_t(); endtask\n"
    "  export \"DPI-C\" c_xt = task x_t;\n"
    "  function int e_f(); return 1; endfunction\n"
    "  export \"DPI-C\" function e_f;\n"
    "  function int d_f(); return 1; endfunction\n"
    "  export \"DPI\" function d_f;\n"
    "  function int s_f(); return 1; endfunction\n"
    "  task s_t(); endtask\n"
    "endmodule\n";

TEST_F(TaskFuncRulesOfARun, EachImportAndExportReportsItsAccess) {
  Run(kDpiForms);
  for (vpiHandle tf : {InPackage("p", "p_f"), InTop("d_t"), InTop("i_t")}) {
    ASSERT_NE(tf, nullptr);
    EXPECT_EQ(vpi_get(vpiAccessType, tf), vpiDPIImportAcc)
        << vpi_get_str(vpiFullName, tf);
  }
  for (vpiHandle tf : {InTop("e_t"), InTop("x_t")}) {
    ASSERT_NE(tf, nullptr);
    EXPECT_EQ(vpi_get(vpiAccessType, tf), vpiDPIExportAcc)
        << vpi_get_str(vpiFullName, tf);
  }
}

TEST_F(TaskFuncRulesOfARun, OnlyAContextImportIsContext) {
  Run(kDpiForms);
  EXPECT_EQ(vpi_get(vpiDPIContext, InTop("c_t")), 1);
  for (const char* name : {"d_t", "i_t", "i_f", "e_f", "e_t", "s_f", "s_t"}) {
    EXPECT_EQ(vpi_get(vpiDPIContext, InTop(name)), 0) << name;
  }
}

TEST_F(TaskFuncRulesOfARun, ADpiExportIsDpiAndADpiCExportIsDpiC) {
  Run(kDpiForms);
  EXPECT_EQ(vpi_get(vpiDPICStr, InTop("d_f")), vpiDPI);
  EXPECT_EQ(vpi_get(vpiDPICStr, InTop("e_f")), vpiDPIC);
}

TEST_F(TaskFuncRulesOfARun, EachImportAndExportNamesItsCLinkage) {
  Run(kDpiForms);
  const struct {
    const char* name;
    const char* linkage;
  } kExpected[] = {{"e_f", "e_f"},
                   {"i_t", "i_t"},
                   {"n_t", "c_it"},
                   {"e_t", "e_t"},
                   {"x_t", "c_xt"}};
  for (const auto& e : kExpected) {
    vpiHandle tf = InTop(e.name);
    ASSERT_NE(tf, nullptr) << e.name;
    EXPECT_STREQ(vpi_get_str(vpiDPICIdentifier, tf), e.linkage) << e.name;
  }
}

TEST_F(TaskFuncRulesOfARun, OnlyAPureImportFunctionIsPure) {
  Run(kDpiForms);
  EXPECT_EQ(vpi_get(vpiDPIPure, InTop("q_f")), 1);
  for (const char* name : {"i_f", "i_t", "c_t", "e_f", "s_f"}) {
    EXPECT_EQ(vpi_get(vpiDPIPure, InTop(name)), 0) << name;
  }
}

}  // namespace
}  // namespace delta
