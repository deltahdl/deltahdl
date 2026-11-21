#include <gtest/gtest.h>

#include <algorithm>
#include <functional>
#include <string>
#include <tuple>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VirtualInterfaceVarsInEveryPlace : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    Probed().clear();
    Watched() = [] { return std::vector<vpiHandle>{}; };
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$probe");
    data.calltf = &ProbeHeld;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }

  static std::vector<VpiObject*>& Probed() {
    static std::vector<VpiObject*> probed;
    return probed;
  }

  static std::function<std::vector<vpiHandle>()>& Watched() {
    static std::function<std::vector<vpiHandle>()> watched;
    return watched;
  }

  static PLI_INT32 ProbeHeld(PLI_BYTE8*) {
    for (vpiHandle var : Watched()()) {
      Probed().push_back(VpiObjectOf(Through(vpiActual, var)));
    }
    return 0;
  }

  static vpiHandle Through(int relation, vpiHandle ref) {
    return ref == nullptr ? nullptr : vpi_handle(relation, ref);
  }

  static vpiHandle Tf(const char* name) {
    return Named(vpiTaskFunc, By("top"), name);
  }

  static vpiHandle Method(const char* cls, const char* name) {
    vpiHandle defn = Named(vpiClassDefn, By("top"), cls);
    return defn == nullptr ? nullptr : Named(vpiMethods, defn, name);
  }

  static vpiHandle Formal(vpiHandle tf, const char* name) {
    return tf == nullptr ? nullptr
                         : Through(vpiExpr, Named(vpiIODecl, tf, name));
  }

  static vpiHandle Local(vpiHandle scope, const char* name) {
    return scope == nullptr ? nullptr
                            : Named(vpiVirtualInterfaceVar, scope, name);
  }

  static vpiHandle Property(const char* name) {
    return Local(Through(vpiClassObj, By("top.c")), name);
  }

  static vpiHandle Modport(const char* inst, const char* name) {
    vpiHandle iface = By(inst);
    return iface == nullptr ? nullptr : Named(vpiModport, iface, name);
  }

  static vpiHandle FirstStmt(vpiHandle tf) {
    vpiHandle body = Through(vpiStmt, tf);
    if (body == nullptr || vpi_get(vpiType, body) != vpiBegin) return body;
    std::vector<vpiHandle> stmts = ObjectsOf(vpiStmt, body);
    return stmts.empty() ? nullptr : stmts.front();
  }

  static std::string InterfaceTypeOf(vpiHandle var) {
    vpiHandle typespec = Through(vpiTypespec, var);
    if (typespec == nullptr) return "<no typespec>";
    if (vpi_get(vpiType, typespec) != vpiInterfaceTypespec) {
      return "<another typespec>";
    }
    const char* def_name = vpi_get_str(vpiDefName, typespec);
    return def_name == nullptr ? "<no vpiDefName>" : def_name;
  }

  static std::vector<std::string> FullNamesOf(int type, vpiHandle ref) {
    std::vector<std::string> names;
    for (vpiHandle obj : ObjectsOf(type, ref)) {
      const char* name = vpi_get_str(vpiFullName, obj);
      names.emplace_back(name == nullptr ? "<null>" : name);
    }
    std::ranges::sort(names);
    return names;
  }
};

constexpr const char* kEveryPlace =
    "interface SBus; logic req; modport phy(input req); endinterface\n"
    "module m(SBus s, SBus.phy sp);\n"
    "  virtual SBus vs = s;\n"
    "  virtual SBus.phy vsp = sp;\n"
    "endmodule\n"
    "module top;\n"
    "  SBus bus();\n"
    "  m u(.s(bus), .sp(bus));\n"
    "  virtual SBus v = bus;\n"
    "  virtual SBus a = v;\n"
    "  virtual SBus vn = null;\n"
    "  virtual SBus v32 [1:2];\n"
    "  class C;\n"
    "    virtual SBus cv;\n"
    "    virtual SBus.phy cp;\n"
    "    virtual SBus ci = bus;\n"
    "    static virtual SBus sv;\n"
    "    function new(virtual SBus b); cv = b; endfunction\n"
    "  endclass\n"
    "  C c;\n"
    "  task automatic t(virtual SBus tb, virtual SBus.phy tp);\n"
    "    virtual SBus tl = bus;\n"
    "    virtual SBus tn;\n"
    "    virtual SBus.phy tlp;\n"
    "  endtask\n"
    "  function automatic void f(virtual SBus.phy fp);\n"
    "    virtual SBus fi = bus;\n"
    "    virtual SBus fl;\n"
    "  endfunction\n"
    "  initial begin : blk\n"
    "    virtual SBus x;\n"
    "    c = new(bus);\n"
    "  end\n"
    "endmodule\n";

constexpr const char* kModports =
    "interface SBus; logic req; modport phy(input req); endinterface\n"
    "module top;\n"
    "  SBus bus();\n"
    "  virtual SBus.phy pm = bus.phy;\n"
    "  virtual SBus.phy pa;\n"
    "  initial pa = bus.phy;\n"
    "endmodule\n";

constexpr const char* kAssignments =
    "interface SBus; logic req; endinterface\n"
    "module top;\n"
    "  SBus bus();\n"
    "  SBus other();\n"
    "  virtual SBus w;\n"
    "  initial begin\n"
    "    $probe;\n"
    "    w = bus;\n"
    "    $probe;\n"
    "    w = other;\n"
    "    $probe;\n"
    "    w = null;\n"
    "    $probe;\n"
    "  end\n"
    "endmodule\n";

constexpr const char* kCalls =
    "interface SBus; logic req; endinterface\n"
    "module top;\n"
    "  SBus bus();\n"
    "  SBus other();\n"
    "  task automatic t(virtual SBus tb); $probe; endtask\n"
    "  initial begin t(bus); t(other); end\n"
    "endmodule\n";

constexpr const char* kTransactor =
    "interface SBus; logic req, grant; endinterface\n"
    "module top;\n"
    "  class SBusTransactor;\n"
    "    virtual SBus bus;\n"
    "    function new(virtual SBus s);\n"
    "      bus = s;\n"
    "      $probe;\n"
    "    endfunction\n"
    "  endclass\n"
    "  SBus s1();\n"
    "  SBus s2();\n"
    "  SBusTransactor t1, t2;\n"
    "  initial begin t1 = new(s1); t2 = new(s2); end\n"
    "endmodule\n";

TEST_F(VirtualInterfaceVarsInEveryPlace,
       DISABLED_AClassPropertyReachesItsInterfaceTypespec) {
  Run(kEveryPlace);
  EXPECT_EQ(InterfaceTypeOf(Property("cv")), "SBus");
  EXPECT_EQ(InterfaceTypeOf(Property("cp")), "phy");
}

TEST_F(VirtualInterfaceVarsInEveryPlace,
       AParameterizedVarReachesTheInterfacesTypespec) {
  Run("interface SBus #(parameter int W = 8); logic [W-1:0] data;\n"
      "endinterface\n"
      "module top;\n"
      "  SBus #(16) b16();\n"
      "  virtual SBus #(16) v16 = b16;\n"
      "endmodule\n");
  EXPECT_EQ(InterfaceTypeOf(By("top.v16")), "SBus");
}

TEST_F(VirtualInterfaceVarsInEveryPlace,
       DISABLED_AFormalReachesItsInterfaceTypespec) {
  Run(kEveryPlace);
  EXPECT_EQ(InterfaceTypeOf(Formal(Tf("t"), "tb")), "SBus");
  EXPECT_EQ(InterfaceTypeOf(Formal(Tf("t"), "tp")), "phy");
  EXPECT_EQ(InterfaceTypeOf(Formal(Tf("f"), "fp")), "phy");
  EXPECT_EQ(InterfaceTypeOf(Formal(Method("C", "new"), "b")), "SBus");
}

TEST_F(VirtualInterfaceVarsInEveryPlace,
       AnUnassignedClassPropertyHoldsNothing) {
  Run(kEveryPlace);
  vpiHandle cp = Property("cp");
  ASSERT_NE(cp, nullptr);
  EXPECT_EQ(vpi_handle(vpiActual, cp), nullptr);
  EXPECT_EQ(VpiObjectOf(Through(vpiActual, Property("cv"))),
            VpiObjectOf(By("top.bus")));
}

TEST_F(VirtualInterfaceVarsInEveryPlace, AVarHoldsWhatItsLatestAssignmentGave) {
  Watched() = [] { return std::vector<vpiHandle>{By("top.w")}; };
  Run(kAssignments);
  EXPECT_EQ(Probed(),
            (std::vector<VpiObject*>{nullptr, VpiObjectOf(By("top.bus")),
                                     VpiObjectOf(By("top.other")), nullptr}));
}

TEST_F(VirtualInterfaceVarsInEveryPlace, DISABLED_AModportVarHoldsTheModport) {
  Run(kModports);
  vpiHandle phy = Modport("top.bus", "phy");
  ASSERT_NE(phy, nullptr);
  for (const char* name : {"top.pm", "top.pa"}) {
    SCOPED_TRACE(name);
    vpiHandle held = Through(vpiActual, By(name));
    ASSERT_NE(held, nullptr);
    EXPECT_EQ(vpi_get(vpiType, held), vpiModport);
    EXPECT_EQ(VpiObjectOf(held), VpiObjectOf(phy));
  }
}

TEST_F(VirtualInterfaceVarsInEveryPlace,
       DISABLED_AFormalHoldsTheArgumentOfTheActiveCall) {
  Watched() = [] { return std::vector<vpiHandle>{Formal(Tf("t"), "tb")}; };
  Run(kCalls);
  EXPECT_EQ(Probed(), (std::vector<VpiObject*>{VpiObjectOf(By("top.bus")),
                                               VpiObjectOf(By("top.other"))}));
}

TEST_F(VirtualInterfaceVarsInEveryPlace,
       DISABLED_AFormalOrLocalOfAModportTypeIsAModport) {
  Run(kEveryPlace);
  for (const auto& [var, is_modport] : {std::tuple{Formal(Tf("t"), "tb"), 0},
                                        std::tuple{Formal(Tf("t"), "tp"), 1},
                                        std::tuple{Local(Tf("t"), "tl"), 0},
                                        std::tuple{Local(Tf("t"), "tlp"), 1},
                                        std::tuple{Formal(Tf("f"), "fp"), 1},
                                        std::tuple{Local(Tf("f"), "fl"), 0}}) {
    ASSERT_NE(var, nullptr);
    SCOPED_TRACE(vpi_get_str(vpiName, var));
    EXPECT_EQ(vpi_get(vpiIsModPort, var), is_modport);
  }
}

TEST_F(VirtualInterfaceVarsInEveryPlace,
       DISABLED_AModportInitializerIsTheModport) {
  Run(kModports);
  vpiHandle phy = Modport("top.bus", "phy");
  ASSERT_NE(phy, nullptr);
  EXPECT_EQ(VpiObjectOf(Through(vpiExpr, By("top.pm"))), VpiObjectOf(phy));
  vpiHandle pa = By("top.pa");
  ASSERT_NE(pa, nullptr);
  EXPECT_EQ(vpi_handle(vpiExpr, pa), nullptr);
}

TEST_F(VirtualInterfaceVarsInEveryPlace, AVarInitializerIsThatVar) {
  Run(kEveryPlace);
  vpiHandle v = By("top.v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(VpiObjectOf(Through(vpiExpr, By("top.a"))), VpiObjectOf(v));
}

TEST_F(VirtualInterfaceVarsInEveryPlace,
       DISABLED_APortInitializerIsARefObjToThePort) {
  Run(kEveryPlace);
  vpiHandle of_s = Through(vpiExpr, By("top.u.vs"));
  ASSERT_NE(of_s, nullptr);
  EXPECT_EQ(vpi_get(vpiType, of_s), vpiRefObj);
  EXPECT_EQ(VpiObjectOf(Through(vpiActual, of_s)), VpiObjectOf(By("top.bus")));
  vpiHandle of_sp = Through(vpiExpr, By("top.u.vsp"));
  ASSERT_NE(of_sp, nullptr);
  EXPECT_EQ(vpi_get(vpiType, of_sp), vpiRefObj);
  vpiHandle phy = Modport("top.bus", "phy");
  ASSERT_NE(phy, nullptr);
  EXPECT_EQ(VpiObjectOf(Through(vpiActual, of_sp)), VpiObjectOf(phy));
}

TEST_F(VirtualInterfaceVarsInEveryPlace,
       DISABLED_ANullInitializerIsANullConstant) {
  Run(kEveryPlace);
  vpiHandle of_vn = Through(vpiExpr, By("top.vn"));
  ASSERT_NE(of_vn, nullptr);
  EXPECT_EQ(vpi_get(vpiType, of_vn), vpiConstant);
  EXPECT_EQ(vpi_get(vpiConstType, of_vn), vpiNullConst);
}

TEST_F(VirtualInterfaceVarsInEveryPlace,
       DISABLED_AClassPropertysInitializerIsItsExpr) {
  Run(kEveryPlace);
  EXPECT_EQ(VpiObjectOf(Through(vpiExpr, Property("ci"))),
            VpiObjectOf(By("top.bus")));
  vpiHandle cv = Property("cv");
  ASSERT_NE(cv, nullptr);
  EXPECT_EQ(vpi_handle(vpiExpr, cv), nullptr);
}

TEST_F(VirtualInterfaceVarsInEveryPlace,
       DISABLED_ASubroutineLocalsInitializerIsItsExpr) {
  Run(kEveryPlace);
  vpiHandle bus = By("top.bus");
  ASSERT_NE(bus, nullptr);
  EXPECT_EQ(VpiObjectOf(Through(vpiExpr, Local(Tf("t"), "tl"))),
            VpiObjectOf(bus));
  EXPECT_EQ(VpiObjectOf(Through(vpiExpr, Local(Tf("f"), "fi"))),
            VpiObjectOf(bus));
  for (vpiHandle bare : {Local(Tf("t"), "tn"), Local(Tf("f"), "fl")}) {
    ASSERT_NE(bare, nullptr);
    EXPECT_EQ(vpi_handle(vpiExpr, bare), nullptr);
  }
}

TEST_F(VirtualInterfaceVarsInEveryPlace, AModuleVarsFullNameFollowsItsModule) {
  Run(kEveryPlace);
  EXPECT_EQ(NamesOf(vpiVirtualInterfaceVar, By("top")),
            (std::vector<std::string>{"a", "v", "v32[1]", "v32[2]", "vn"}));
  EXPECT_EQ(FullNamesOf(vpiVirtualInterfaceVar, By("top")),
            (std::vector<std::string>{"top.a", "top.v", "top.v32[1]",
                                      "top.v32[2]", "top.vn"}));
}

TEST_F(VirtualInterfaceVarsInEveryPlace, AClassPropertyHasANameButNoFullName) {
  Run(kEveryPlace);
  for (const char* name : {"cv", "cp"}) {
    vpiHandle property = Property(name);
    ASSERT_NE(property, nullptr) << name;
    EXPECT_STREQ(vpi_get_str(vpiName, property), name);
    EXPECT_EQ(vpi_get_str(vpiFullName, property), nullptr) << name;
  }
}

TEST_F(VirtualInterfaceVarsInEveryPlace,
       AStaticClassPropertyIsNamedThroughItsClass) {
  Run(kEveryPlace);
  vpiHandle sv = By("top.C::sv");
  ASSERT_NE(sv, nullptr);
  EXPECT_EQ(vpi_get(vpiType, sv), vpiVirtualInterfaceVar);
  EXPECT_STREQ(vpi_get_str(vpiName, sv), "sv");
  EXPECT_STREQ(vpi_get_str(vpiFullName, sv), "top.C::sv");
}

TEST_F(VirtualInterfaceVarsInEveryPlace,
       ASubroutineOrBlockVarsFullNameFollowsItsScope) {
  Run(kEveryPlace);
  for (const auto& [var, name, full_name] :
       {std::tuple{Formal(Tf("t"), "tb"), "tb", "top.t.tb"},
        std::tuple{Local(Tf("t"), "tl"), "tl", "top.t.tl"},
        std::tuple{Formal(Tf("f"), "fp"), "fp", "top.f.fp"},
        std::tuple{Local(Tf("f"), "fl"), "fl", "top.f.fl"},
        std::tuple{Formal(Method("C", "new"), "b"), "b", "top.C::new.b"},
        std::tuple{Local(By("top.blk"), "x"), "x", "top.blk.x"}}) {
    SCOPED_TRACE(full_name);
    ASSERT_NE(var, nullptr);
    EXPECT_EQ(vpi_get(vpiType, var), vpiVirtualInterfaceVar);
    EXPECT_STREQ(vpi_get_str(vpiName, var), name);
    EXPECT_STREQ(vpi_get_str(vpiFullName, var), full_name);
  }
}

TEST_F(VirtualInterfaceVarsInEveryPlace,
       TheConstructorsLeftSideIsThePropertyItAssigns) {
  Run(kTransactor);
  vpiHandle assign = FirstStmt(Method("SBusTransactor", "new"));
  ASSERT_NE(assign, nullptr);
  EXPECT_EQ(vpi_get(vpiType, assign), vpiAssignment);
  vpiHandle lhs = vpi_handle(vpiLhs, assign);
  ASSERT_NE(lhs, nullptr);
  EXPECT_EQ(vpi_get(vpiType, lhs), vpiVirtualInterfaceVar);
  EXPECT_STREQ(vpi_get_str(vpiName, lhs), "bus");
  EXPECT_EQ(InterfaceTypeOf(lhs), "SBus");
}

TEST_F(VirtualInterfaceVarsInEveryPlace,
       DISABLED_TheConstructorsLeftSideHoldsTheInstanceOfItsCall) {
  Watched() = [] {
    return std::vector<vpiHandle>{
        Through(vpiLhs, FirstStmt(Method("SBusTransactor", "new")))};
  };
  Run(kTransactor);
  EXPECT_EQ(Probed(), (std::vector<VpiObject*>{VpiObjectOf(By("top.s1")),
                                               VpiObjectOf(By("top.s2"))}));
}

TEST_F(VirtualInterfaceVarsInEveryPlace,
       DISABLED_TheConstructorsRightSideHoldsTheArgumentPassed) {
  Watched() = [] {
    return std::vector<vpiHandle>{
        Through(vpiRhs, FirstStmt(Method("SBusTransactor", "new")))};
  };
  Run(kTransactor);
  vpiHandle rhs = Through(vpiRhs, FirstStmt(Method("SBusTransactor", "new")));
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(vpi_get(vpiType, rhs), vpiVirtualInterfaceVar);
  EXPECT_STREQ(vpi_get_str(vpiName, rhs), "s");
  EXPECT_EQ(Probed(), (std::vector<VpiObject*>{VpiObjectOf(By("top.s1")),
                                               VpiObjectOf(By("top.s2"))}));
}

}  // namespace
}  // namespace delta
