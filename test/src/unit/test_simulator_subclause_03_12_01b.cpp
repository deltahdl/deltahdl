#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "helpers_dpi_c_binding.h"
#include "helpers_separate_units.h"
#include "simulator/dpi_binding.h"
#include "simulator/dpi_runtime.h"
#include "simulator/lowerer.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/unit_scopes.h"
#include "simulator/variable.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

using namespace delta;

namespace {

RtlirDesign* LowerUnits(const std::vector<std::string>& srcs, SimFixture& f) {
  Elaborator elab(f.arena, f.diag,
                  ParseUnitsApart(srcs, f.mgr, f.arena, f.diag));
  auto* design = elab.Elaborate("");
  EXPECT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  if (design == nullptr) return nullptr;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  return design;
}

uint64_t ValueOf(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  EXPECT_NE(var, nullptr) << name;
  return var == nullptr ? 0 : var->value.ToUint64();
}

std::vector<uint64_t> RunTopAndChild(const std::vector<std::string>& srcs) {
  SimFixture f;
  if (LowerUnits(srcs, f) == nullptr) return {};
  f.scheduler.Run();
  return {ValueOf(f, "a"), ValueOf(f, "c.b")};
}

TEST(SeparateUnitsSim, EachUnitsVariableIsItsOwn) {
  SimFixture f;
  ASSERT_NE(LowerUnits({"int g = 1;\n"
                        "module top;\n"
                        "  int a, sa;\n"
                        "  child c();\n"
                        "  initial begin a = g; sa = $unit::g; end\n"
                        "endmodule\n",
                        "int g = 2;\n"
                        "module child;\n"
                        "  int b, sb;\n"
                        "  initial begin b = g; sb = $unit::g; end\n"
                        "endmodule\n"},
                       f),
            nullptr);
  f.scheduler.Run();
  EXPECT_EQ(ValueOf(f, "a"), 1u);
  EXPECT_EQ(ValueOf(f, "sa"), 1u);
  EXPECT_EQ(ValueOf(f, "c.b"), 2u);
  EXPECT_EQ(ValueOf(f, "c.sb"), 2u);
}

TEST(SeparateUnitsSim, EachUnitsNetIsItsOwn) {
  SimFixture f;
  ASSERT_NE(LowerUnits({"wire [3:0] w;\n"
                        "module top;\n"
                        "  logic [3:0] a, sa;\n"
                        "  child c();\n"
                        "  assign w = 4'd1;\n"
                        "  initial #1 begin a = w; sa = $unit::w; end\n"
                        "endmodule\n",
                        "wire [3:0] w;\n"
                        "module child;\n"
                        "  logic [3:0] b, sb;\n"
                        "  assign w = 4'd2;\n"
                        "  initial #1 begin b = w; sb = $unit::w; end\n"
                        "endmodule\n"},
                       f),
            nullptr);
  f.scheduler.Run();
  EXPECT_EQ(ValueOf(f, "a"), 1u);
  EXPECT_EQ(ValueOf(f, "sa"), 1u);
  EXPECT_EQ(ValueOf(f, "c.b"), 2u);
  EXPECT_EQ(ValueOf(f, "c.sb"), 2u);
}

TEST(SeparateUnitsSim, EachUnitsFunctionIsItsOwn) {
  SimFixture f;
  ASSERT_NE(LowerUnits({"function int f(); return 10; endfunction\n"
                        "module top;\n"
                        "  int a;\n"
                        "  child c();\n"
                        "  initial a = f();\n"
                        "endmodule\n",
                        "function int f(); return 20; endfunction\n"
                        "function int via(); return f(); endfunction\n"
                        "module child;\n"
                        "  int b, bv;\n"
                        "  initial begin b = f(); bv = via(); end\n"
                        "endmodule\n"},
                       f),
            nullptr);
  f.scheduler.Run();
  EXPECT_EQ(ValueOf(f, "a"), 10u);
  EXPECT_EQ(ValueOf(f, "c.b"), 20u);
  EXPECT_EQ(ValueOf(f, "c.bv"), 20u);
}

TEST(SeparateUnitsSim, EachUnitsClassIsItsOwn) {
  EXPECT_EQ(RunTopAndChild({"package q; class K; endclass endpackage\n"
                            "class C; int v = 3; endclass\n"
                            "module top;\n"
                            "  int a;\n"
                            "  C h;\n"
                            "  child c();\n"
                            "  initial begin h = new; a = h.v; end\n"
                            "endmodule\n",
                            "class C; int v = 4; endclass\n"
                            "class D; endclass\n"
                            "module child;\n"
                            "  int b;\n"
                            "  C h;\n"
                            "  initial begin h = new; b = h.v; end\n"
                            "endmodule\n"}),
            (std::vector<uint64_t>{3, 4}));
}

TEST(SeparateUnitsSim, EachUnitsTypedefIsItsOwn) {
  EXPECT_EQ(RunTopAndChild({"package q; typedef int qt; endpackage\n"
                            "typedef logic [3:0] t;\n"
                            "module top;\n"
                            "  int a;\n"
                            "  int x = 255;\n"
                            "  child c();\n"
                            "  initial a = t'(x);\n"
                            "endmodule\n",
                            "typedef logic [5:0] t;\n"
                            "module child;\n"
                            "  int b;\n"
                            "  int x = 255;\n"
                            "  initial b = t'(x);\n"
                            "endmodule\n"}),
            (std::vector<uint64_t>{15, 63}));
}

TEST(SeparateUnitsSim, EachUnitsCovergroupIsItsOwn) {
  EXPECT_EQ(RunTopAndChild({"covergroup cg with function sample(int v);\n"
                            "  coverpoint v { bins b[] = {[0:1]}; }\n"
                            "endgroup\n"
                            "module top;\n"
                            "  int a;\n"
                            "  child c();\n"
                            "  initial begin\n"
                            "    automatic cg k = new;\n"
                            "    k.sample(0);\n"
                            "    a = int'(k.get_inst_coverage());\n"
                            "  end\n"
                            "endmodule\n",
                            "covergroup cg with function sample(int v);\n"
                            "  coverpoint v { bins b[] = {[0:3]}; }\n"
                            "endgroup\n"
                            "module child;\n"
                            "  int b;\n"
                            "  initial begin\n"
                            "    automatic cg k = new;\n"
                            "    k.sample(0);\n"
                            "    b = int'(k.get_inst_coverage());\n"
                            "  end\n"
                            "endmodule\n"}),
            (std::vector<uint64_t>{50, 25}));
}

TEST(SeparateUnitsSim, EachUnitsLetIsItsOwn) {
  EXPECT_EQ(RunTopAndChild({"let f(x) = x + 1;\n"
                            "module top;\n"
                            "  int a;\n"
                            "  child c();\n"
                            "  initial a = f(4);\n"
                            "endmodule\n",
                            "let f(x) = x * 10;\n"
                            "module child;\n"
                            "  int b;\n"
                            "  initial b = f(4);\n"
                            "endmodule\n"}),
            (std::vector<uint64_t>{5, 40}));
}

int SeparateUnitsAddOne(int x) { return x + 1; }
int SeparateUnitsAddTwo(int x) { return x + 2; }
int SeparateUnitsAddThree(int x) { return x + 3; }

TEST(SeparateUnitsSim, EachUnitsDpiImportIsItsOwn) {
  SimFixture f;
  auto* design = LowerUnits(
      {"import \"DPI-C\" add_one = function int f(input int x);\n"
       "module top;\n"
       "  int a;\n"
       "  child c();\n"
       "  initial a = f(10);\n"
       "endmodule\n",
       "import \"DPI-C\" add_two = function int f(input int x);\n"
       "module child;\n"
       "  import \"DPI-C\" add_three = function int h(input int x);\n"
       "  int b, bh;\n"
       "  initial begin b = f(10); bh = h(10); end\n"
       "endmodule\n"},
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_NE(f.ctx.GetDpiRuntime(), nullptr);
  const auto* second = f.ctx.GetDpiRuntime()->FindImportIn("$unit#1", "f");
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(second->c_name, "add_two");
  EXPECT_EQ(f.ctx.Units().UnitOf("c."), 1);
  BindDpiImports(
      *f.ctx.GetDpiRuntime(),
      LookupIn(
          {{"add_one", reinterpret_cast<void*>(&SeparateUnitsAddOne)},
           {"add_two", reinterpret_cast<void*>(&SeparateUnitsAddTwo)},
           {"add_three", reinterpret_cast<void*>(&SeparateUnitsAddThree)}}),
      CallBuildDir("separate_units_dpi"), "cc", f.diag);
  f.scheduler.Run();
  EXPECT_EQ(ValueOf(f, "a"), 11u);
  EXPECT_EQ(ValueOf(f, "c.b"), 12u);
  EXPECT_EQ(ValueOf(f, "c.bh"), 13u);
}

TEST(SeparateUnitsSim, EachUnitsImportIsItsOwn) {
  EXPECT_EQ(RunTopAndChild({"package p1; int x = 5; endpackage\n"
                            "import p1::*;\n"
                            "module top;\n"
                            "  int a;\n"
                            "  child c();\n"
                            "  initial a = x;\n"
                            "endmodule\n",
                            "package p2; int x = 6; endpackage\n"
                            "import p2::*;\n"
                            "module child;\n"
                            "  int b;\n"
                            "  initial b = x;\n"
                            "endmodule\n"}),
            (std::vector<uint64_t>{5, 6}));
}

TEST(SeparateUnitsSim, InstanceUnitIsTheNearestRecordedHolder) {
  UnitScopes units;
  units.SetInstanceUnit("", -1);
  EXPECT_FALSE(units.Separate());
  EXPECT_EQ(units.UnitOf("c."), -1);
  units.SetInstanceUnit("", 0);
  units.SetInstanceUnit("c.", 1);
  EXPECT_TRUE(units.Separate());
  EXPECT_EQ(units.UnitOf(""), 0);
  EXPECT_EQ(units.UnitOf("c.g."), 1);
  EXPECT_EQ(units.UnitOf("d."), 0);
  EXPECT_EQ(UnitScopes::ScopeName(-1), "$unit");
  EXPECT_EQ(UnitScopes::ScopeName(2), "$unit#2");
  EXPECT_TRUE(UnitScopes::IsUnitScope("$unit#2"));
  EXPECT_FALSE(UnitScopes::IsUnitScope("pkg"));
}

TEST(SeparateUnitsSim, EachUnitsClassKeepsItsOwnStatics) {
  EXPECT_EQ(RunTopAndChild({"class C; static int s = 5; endclass\n"
                            "module top;\n"
                            "  int a;\n"
                            "  child c();\n"
                            "  initial a = C::s;\n"
                            "endmodule\n",
                            "class C; static int s = 7; endclass\n"
                            "module child;\n"
                            "  int b;\n"
                            "  initial b = C::s;\n"
                            "endmodule\n"}),
            (std::vector<uint64_t>{5, 7}));
}

TEST(SeparateUnitsSim, EachUnitsTaskRunsInItsOwnTimeScale) {
  EXPECT_EQ(RunTopAndChild({"timeunit 1ns;\n"
                            "timeprecision 1ps;\n"
                            "task automatic t0(); #1; endtask\n"
                            "module top;\n"
                            "  int a;\n"
                            "  child c();\n"
                            "  initial begin t0(); a = $time; end\n"
                            "endmodule\n",
                            "timeunit 10ns;\n"
                            "timeprecision 1ps;\n"
                            "task automatic t1(); #1; endtask\n"
                            "module child;\n"
                            "  int b;\n"
                            "  initial begin t1(); b = $time; end\n"
                            "endmodule\n",
                            "typedef int unused_t;\n"}),
            (std::vector<uint64_t>{1, 1}));
}

using NamesByUnit = std::vector<std::vector<std::string>>;

std::vector<std::string> UnitsOfOneName(std::string_view top_items,
                                        std::string_view child_items) {
  const std::string kOwn =
      "function int f(); return 1; endfunction\n"
      "task t(); endtask\n";
  return {"int mark0;\n" + kOwn + "module top; child c();\n" +
              std::string(top_items) + "endmodule\n",
          "int mark1;\n" + kOwn + "module child;\n" + std::string(child_items) +
              "endmodule\n",
          "module other; endmodule\n"};
}

class SeparateUnitsVpi : public VpiDesignRun {
 protected:
  void RunUnits(const std::vector<std::string>& srcs) {
    Elaborator elab(f_.arena, f_.diag,
                    ParseUnitsApart(srcs, f_.mgr, f_.arena, f_.diag));
    auto* design = elab.Elaborate("");
    ASSERT_NE(design, nullptr);
    ASSERT_FALSE(f_.diag.HasErrors());
    LowerAndRun(design, f_);
  }

  static NamesByUnit NamesPerUnit(int type) {
    NamesByUnit reached;
    for (vpiHandle pkg : ObjectsOf(vpiPackage, nullptr)) {
      reached.push_back(NamesOf(type, pkg));
    }
    std::ranges::sort(reached);
    return reached;
  }

  static VpiObject* UnitMarked(std::string_view marker) {
    for (vpiHandle pkg : ObjectsOf(vpiPackage, nullptr)) {
      if (Named(vpiVariables, pkg, marker) != nullptr) return VpiObjectOf(pkg);
    }
    return nullptr;
  }

  static VpiObject* UnitOfCallee(vpiHandle call, int relation) {
    vpiHandle callee = call == nullptr ? nullptr : vpi_handle(relation, call);
    return callee == nullptr ? nullptr : VpiObjectOf(callee)->parent;
  }

  static void ExpectUnitFullNames(int type) {
    for (vpiHandle pkg : ObjectsOf(vpiPackage, nullptr)) {
      for (vpiHandle obj : ObjectsOf(type, pkg)) {
        EXPECT_EQ(std::string(vpi_get_str(vpiFullName, obj)),
                  "$unit::" + std::string(vpi_get_str(vpiName, obj)));
      }
    }
  }
};

TEST_F(SeparateUnitsVpi, EachUnitIsACompilationUnitScope) {
  RunUnits(
      {"int g = 3;\n"
       "module top; int x = $unit::g; child c(); endmodule\n",
       "int g = 4;\n"
       "module child; int y = $unit::g; endmodule\n",
       "module other; endmodule\n"});
  std::vector<int> values;
  vpiHandle it = vpi_iterate(vpiPackage, nullptr);
  ASSERT_NE(it, nullptr);
  while (vpiHandle pkg = vpi_scan(it)) {
    vpiHandle g = Named(vpiVariables, pkg, "g");
    if (g == nullptr) continue;
    EXPECT_STREQ(vpi_get_str(vpiName, pkg), "$unit");
    EXPECT_EQ(FullNameOfChild(pkg, "g"), "$unit::g");
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(g, &value);
    values.push_back(value.value.integer);
  }
  std::ranges::sort(values);
  EXPECT_EQ(values, (std::vector<int>{3, 4}));
}

TEST_F(SeparateUnitsVpi, EachUnitsLetIsALetDeclOfItsOwnScope) {
  RunUnits(
      {"let g(y) = y + 1;\n"
       "module top; logic [3:0] a, w; assign w = g(a); child c();\n"
       "endmodule\n",
       "let h(y) = y + 2;\n"
       "module child; logic [3:0] b, v; assign v = h(b); endmodule\n",
       "module other; endmodule\n"});
  const auto kUsed = [](vpiHandle scope) -> VpiObject* {
    vpiHandle assigns = vpi_iterate(vpiContAssign, scope);
    vpiHandle assign = assigns == nullptr ? nullptr : vpi_scan(assigns);
    vpiHandle used = assign == nullptr ? nullptr : vpi_handle(vpiRhs, assign);
    if (used == nullptr || vpi_get(vpiType, used) != vpiLetExpr) return nullptr;
    return VpiObjectOf(vpi_handle(vpiLetDecl, used));
  };
  VpiObject* g = kUsed(By("top"));
  VpiObject* h = kUsed(By("top.c"));
  ASSERT_NE(g, nullptr);
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(g->name, "g");
  EXPECT_EQ(h->name, "h");
  ASSERT_NE(g->parent, nullptr);
  ASSERT_NE(h->parent, nullptr);
  EXPECT_NE(g->parent, h->parent);
  EXPECT_EQ(g->parent->name, "$unit");
  EXPECT_EQ(h->parent->name, "$unit");
}

TEST_F(SeparateUnitsVpi, EachUnitsNettypeIsANettypeDeclOfItsOwnScope) {
  RunUnits(
      {"nettype logic una;\n"
       "module top; child c(); endmodule\n",
       "nettype logic unb;\n"
       "module child; endmodule\n",
       "module other; endmodule\n"});
  EXPECT_EQ(NamesPerUnit(vpiNetTypedef), (NamesByUnit{{}, {"una"}, {"unb"}}));
}

TEST_F(SeparateUnitsVpi, AUnitDeclaringNothingIsReachedBesideTheOthers) {
  RunUnits(
      {"int g = 3;\n"
       "module top; child c(); endmodule\n",
       "int h = 4;\n"
       "module child; endmodule\n",
       "module other; endmodule\n"});
  int units = 0;
  for (vpiHandle pkg : ObjectsOf(vpiPackage, nullptr)) {
    EXPECT_EQ(vpi_get(vpiUnit, pkg), 1);
    EXPECT_STREQ(vpi_get_str(vpiName, pkg), "$unit");
    ++units;
  }
  EXPECT_EQ(units, 3);
}

TEST_F(SeparateUnitsVpi, EachUnitsTaskOrFunctionIsATaskFuncOfItsOwnScope) {
  RunUnits(
      {"function int f(); return 1; endfunction\n"
       "module top; child c(); endmodule\n",
       "task t(); endtask\n"
       "module child; endmodule\n",
       "module other; endmodule\n"});
  EXPECT_EQ(NamesPerUnit(vpiTaskFunc), (NamesByUnit{{}, {"f"}, {"t"}}));
  ExpectUnitFullNames(vpiTaskFunc);
}

TEST_F(SeparateUnitsVpi, TwoUnitsFunctionsOfOneNameAreEachTheirOwn) {
  RunUnits(
      {"function int f(); return 1; endfunction\n"
       "module top; child c(); endmodule\n",
       "function int f(); return 2; endfunction\n"
       "module child; endmodule\n",
       "module other; endmodule\n"});
  int found = 0;
  for (vpiHandle pkg : ObjectsOf(vpiPackage, nullptr)) {
    vpiHandle f = Named(vpiTaskFunc, pkg, "f");
    if (f == nullptr) continue;
    EXPECT_EQ(VpiObjectOf(f)->parent, VpiObjectOf(pkg));
    ++found;
  }
  EXPECT_EQ(found, 2);
}

TEST_F(SeparateUnitsVpi, AUnitsDpiImportIsATaskFuncOfItsOwnScope) {
  RunUnits({"module top; child c(); endmodule\n",
            "import \"DPI-C\" function int c_f(input int a);\n"
            "module child; endmodule\n",
            "module other; endmodule\n"});
  EXPECT_EQ(NamesPerUnit(vpiTaskFunc), (NamesByUnit{{}, {}, {"c_f"}}));
  ExpectUnitFullNames(vpiTaskFunc);
}

TEST_F(SeparateUnitsVpi, AUnitsClassIsAClassDefnOfItsOwnScope) {
  RunUnits({"module top; child c(); endmodule\n",
            "class C; endclass\n"
            "module child; endmodule\n",
            "module other; endmodule\n"});
  EXPECT_EQ(NamesPerUnit(vpiClassDefn), (NamesByUnit{{}, {}, {"C"}}));
  ExpectUnitFullNames(vpiClassDefn);
}

TEST_F(SeparateUnitsVpi, AUnitsTypedefIsATypespecOfItsOwnScope) {
  RunUnits(
      {"typedef logic [3:0] nib_t;\n"
       "module top; child c(); endmodule\n",
       "module child; endmodule\n", "module other; endmodule\n"});
  EXPECT_EQ(NamesPerUnit(vpiTypedef), (NamesByUnit{{}, {}, {"nib_t"}}));
  ExpectUnitFullNames(vpiTypedef);
}

TEST_F(SeparateUnitsVpi, AModulesCallReachesItsOwnUnitsFunction) {
  RunUnits(UnitsOfOneName("initial begin : b void'(f()); end\n",
                          "initial begin : b void'(f()); end\n"));
  ASSERT_NE(UnitMarked("mark0"), nullptr);
  ASSERT_NE(UnitMarked("mark1"), nullptr);
  EXPECT_EQ(UnitOfCallee(CallOf(vpiFuncCall, By("top.b"), "f"), vpiFunction),
            UnitMarked("mark0"));
  EXPECT_EQ(UnitOfCallee(CallOf(vpiFuncCall, By("top.c.b"), "f"), vpiFunction),
            UnitMarked("mark1"));
}

TEST_F(SeparateUnitsVpi, AModulesTaskEnableReachesItsOwnUnitsTask) {
  RunUnits(UnitsOfOneName("initial begin : b t(); end\n",
                          "initial begin : b t(); end\n"));
  ASSERT_NE(UnitMarked("mark1"), nullptr);
  EXPECT_EQ(UnitOfCallee(CallOf(vpiTaskCall, By("top.b"), "t"), vpiTask),
            UnitMarked("mark0"));
  EXPECT_EQ(UnitOfCallee(CallOf(vpiTaskCall, By("top.c.b"), "t"), vpiTask),
            UnitMarked("mark1"));
}

TEST_F(SeparateUnitsVpi, AGenerateBlocksCallReachesItsOwnUnitsFunction) {
  RunUnits(UnitsOfOneName(
      "", "if (1) begin : g\n  initial begin : b void'(f()); end\nend\n"));
  ASSERT_NE(UnitMarked("mark1"), nullptr);
  EXPECT_EQ(
      UnitOfCallee(CallOf(vpiFuncCall, By("top.c.g.b"), "f"), vpiFunction),
      UnitMarked("mark1"));
}

TEST_F(SeparateUnitsVpi, AModuleTasksCallReachesItsOwnUnitsFunction) {
  RunUnits(UnitsOfOneName("", "task k(); void'(f()); endtask\n"));
  vpiHandle k = Named(vpiTaskFunc, By("top.c"), "k");
  ASSERT_NE(k, nullptr);
  ASSERT_NE(UnitMarked("mark1"), nullptr);
  EXPECT_EQ(UnitOfCallee(vpi_handle(vpiStmt, k), vpiFunction),
            UnitMarked("mark1"));
}

TEST_F(SeparateUnitsVpi, AContinuousAssignmentsCallReachesItsOwnUnitsFunction) {
  RunUnits(UnitsOfOneName("", "wire [31:0] y;\nassign y = f();\n"));
  const std::vector<vpiHandle> kAssigns = ObjectsOf(vpiContAssign, By("top.c"));
  ASSERT_EQ(kAssigns.size(), 1U);
  ASSERT_NE(UnitMarked("mark1"), nullptr);
  EXPECT_EQ(UnitOfCallee(vpi_handle(vpiRhs, kAssigns[0]), vpiFunction),
            UnitMarked("mark1"));
}

TEST_F(SeparateUnitsVpi, AnInterfacesAndAProgramsCallsReachTheirUnitsFunction) {
  RunUnits(
      {"int mark0;\n"
       "function int f(); return 1; endfunction\n"
       "module top; child c(); endmodule\n",
       "int mark1;\n"
       "function int f(); return 2; endfunction\n"
       "interface ifc; initial begin : b void'(f()); end endinterface\n"
       "program pg; initial begin : b void'(f()); end endprogram\n"
       "module child; ifc i(); pg p(); endmodule\n",
       "module other; endmodule\n"});
  ASSERT_NE(UnitMarked("mark1"), nullptr);
  EXPECT_EQ(
      UnitOfCallee(CallOf(vpiFuncCall, By("top.c.i.b"), "f"), vpiFunction),
      UnitMarked("mark1"));
  EXPECT_EQ(
      UnitOfCallee(CallOf(vpiFuncCall, By("top.c.p.b"), "f"), vpiFunction),
      UnitMarked("mark1"));
}

TEST_F(SeparateUnitsVpi, AUnitTasksCallReachesItsOwnUnitsFunction) {
  RunUnits(
      {"function int f(); return 1; endfunction\n"
       "task u(); void'(f()); endtask\n"
       "module top; child c(); endmodule\n",
       "function int f(); return 2; endfunction\n"
       "task u(); void'(f()); endtask\n"
       "module child; endmodule\n",
       "module other; endmodule\n"});
  int walked = 0;
  for (vpiHandle pkg : ObjectsOf(vpiPackage, nullptr)) {
    vpiHandle u = Named(vpiTaskFunc, pkg, "u");
    if (u == nullptr) continue;
    EXPECT_EQ(UnitOfCallee(vpi_handle(vpiStmt, u), vpiFunction),
              VpiObjectOf(pkg));
    ++walked;
  }
  EXPECT_EQ(walked, 2);
}

TEST_F(SeparateUnitsVpi, AModulesDpiCallReachesItsOwnUnitsImport) {
  RunUnits(
      {"int mark0;\n"
       "import \"DPI-C\" function int c_f();\n"
       "module top; child c(); endmodule\n",
       "int mark1;\n"
       "import \"DPI-C\" function int c_f();\n"
       "module child; initial if (0) begin : b void'(c_f()); end\n"
       "endmodule\n",
       "module other; endmodule\n"});
  ASSERT_NE(UnitMarked("mark1"), nullptr);
  EXPECT_EQ(
      UnitOfCallee(CallOf(vpiFuncCall, By("top.c.b"), "c_f"), vpiFunction),
      UnitMarked("mark1"));
}

}  // namespace
