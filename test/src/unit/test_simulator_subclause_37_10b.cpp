#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "fixture_vpi_run.h"
#include "helpers_sealed_design_run.h"
#include "preprocessor/protect_processing.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class InstanceItemsOfARun : public VpiDesignRun {
 protected:
  static vpiHandle Unit() {
    for (vpiHandle pkg : ObjectsOf(vpiPackage, nullptr)) {
      if (vpi_get(vpiUnit, pkg) == 1) return pkg;
    }
    return nullptr;
  }

  static vpiHandle InstanceOf(vpiHandle obj) {
    return vpi_handle(vpiInstance, obj);
  }
};

constexpr const char* kInterfaceAndProgram =
    "interface ifc; endinterface\n"
    "program prg; endprogram\n"
    "module sub; ifc i0(); endmodule\n"
    "module top; ifc i0(); prg p0(); sub m1(); endmodule\n";

TEST_F(InstanceItemsOfARun, InterfaceAndProgramInstancesHaveTheirFullNames) {
  Run(kInterfaceAndProgram);
  EXPECT_STREQ(vpi_get_str(vpiFullName, By("top.i0")), "top.i0");
  EXPECT_STREQ(vpi_get_str(vpiFullName, By("top.p0")), "top.p0");
  EXPECT_STREQ(vpi_get_str(vpiFullName, By("top.m1.i0")), "top.m1.i0");
}

TEST_F(InstanceItemsOfARun, AModuleIteratesItsProgramArrays) {
  Run("program prg; endprogram\n"
      "module top; prg ps[0:1](); prg lone(); endmodule\n");
  EXPECT_EQ(NamesOf(vpiProgramArray, By("top")),
            std::vector<std::string>{"ps"});
  EXPECT_EQ(vpi_get(vpiType, Named(vpiProgramArray, By("top"), "ps")),
            vpiProgramArray);
}

TEST_F(InstanceItemsOfARun, AModuleIteratesItsArrayVariablesAsRegArrays) {
  Run("module top; logic [7:0] mem [0:3]; logic [7:0] flat; endmodule\n");
  EXPECT_EQ(NamesOf(vpiRegArray, By("top")), std::vector<std::string>{"mem"});
}

TEST_F(InstanceItemsOfARun, EveryInstanceKindIteratesItsNamedEvents) {
  Run("package pk; event pe; endpackage\n"
      "interface ifc; event ie; endinterface\n"
      "program prg; event qe; endprogram\n"
      "module top; event me; event arr[0:1]; ifc i0(); prg p0(); endmodule\n");
  EXPECT_EQ(NamesOf(vpiNamedEvent, By("top")), std::vector<std::string>{"me"});
  EXPECT_EQ(NamesOf(vpiNamedEvent, By("top.i0")),
            std::vector<std::string>{"ie"});
  EXPECT_EQ(NamesOf(vpiNamedEvent, By("top.p0")),
            std::vector<std::string>{"qe"});
  EXPECT_EQ(NamesOf(vpiNamedEvent, By("pk")), std::vector<std::string>{"pe"});
  EXPECT_EQ(NamesOf(vpiNamedEventArray, By("top")),
            std::vector<std::string>{"arr"});
}

constexpr const char* kItemsOfEveryKind =
    "interface ifc(input logic clk); wire w; int v; parameter int P = 1;\n"
    "  typedef logic [1:0] two_t; event e;\n"
    "  task t; endtask\n"
    "  a1: assert property (@(posedge clk) v == v);\n"
    "endinterface\n"
    "program prg(input logic clk); wire w; int v; parameter int P = 1;\n"
    "  typedef logic [1:0] two_t; event e;\n"
    "  task t; endtask\n"
    "  a1: assert property (@(posedge clk) v == v);\n"
    "endprogram\n"
    "module top; logic clk; ifc i0(clk); prg p0(clk); endmodule\n";

TEST_F(InstanceItemsOfARun, InterfacesAndProgramsIterateTheirItems) {
  Run(kItemsOfEveryKind);
  for (const char* inst : {"top.i0", "top.p0"}) {
    vpiHandle h = By(inst);
    ASSERT_NE(h, nullptr) << inst;
    EXPECT_EQ(NamesOf(vpiNet, h), (std::vector<std::string>{"clk", "w"}))
        << inst;
    EXPECT_EQ(NamesOf(vpiVariables, h), std::vector<std::string>{"v"}) << inst;
    EXPECT_EQ(NamesOf(vpiTaskFunc, h), std::vector<std::string>{"t"}) << inst;
    EXPECT_EQ(NamesOf(vpiParameter, h), std::vector<std::string>{"P"}) << inst;
    EXPECT_EQ(NamesOf(vpiAssertion, h), std::vector<std::string>{"a1"}) << inst;
    EXPECT_EQ(NamesOf(vpiNamedEvent, h), std::vector<std::string>{"e"}) << inst;
    EXPECT_EQ(NamesOf(vpiTypedef, h), std::vector<std::string>{"two_t"})
        << inst;
  }
}

constexpr const char* kArraysAndLoners =
    "interface ifc; endinterface\n"
    "program prg; endprogram\n"
    "module sub; endmodule\n"
    "module top; sub u(); sub us[0:1](); ifc i(); ifc is[0:1]();\n"
    "  prg p(); prg ps[0:1](); endmodule\n";

TEST_F(InstanceItemsOfARun, OnlyArrayElementsAreArrayMembers) {
  Run(kArraysAndLoners);
  for (const char* name : {"top.us[1]", "top.is[1]", "top.ps[1]"}) {
    EXPECT_EQ(vpi_get(vpiArrayMember, By(name)), 1) << name;
  }
  for (const char* name : {"top", "top.u", "top.i", "top.p"}) {
    EXPECT_EQ(vpi_get(vpiArrayMember, By(name)), 0) << name;
  }
}

TEST_F(InstanceItemsOfARun,
       DISABLED_TheDeprecatedArrayPropertyMatchesMembership) {
  Run(kArraysAndLoners);
  for (const char* name : {"top.us[1]", "top.is[1]", "top.ps[1]"}) {
    EXPECT_EQ(vpi_get(vpiArray, By(name)), 1) << name;
  }
  for (const char* name : {"top", "top.u", "top.i", "top.p"}) {
    EXPECT_EQ(vpi_get(vpiArray, By(name)), 0) << name;
  }
}

TEST_F(InstanceItemsOfARun, InterfacesAndProgramsReachTheirNettypes) {
  Run("interface ifc; nettype logic [3:0] int_nt; endinterface\n"
      "program prg; nettype logic [3:0] prg_nt; endprogram\n"
      "module top; ifc i0(); prg p0(); endmodule\n");
  EXPECT_EQ(NamesOf(vpiNetTypedef, By("top.i0")),
            std::vector<std::string>{"int_nt"});
  EXPECT_EQ(NamesOf(vpiNetTypedef, By("top.p0")),
            std::vector<std::string>{"prg_nt"});
}

constexpr std::string_view kInstanceKey = "instance-exchange-key";

TEST_F(InstanceItemsOfARun, DISABLED_AnInstanceOfASealedModuleIsProtected) {
  RunUnderKey(EncryptEnvelopes("`pragma protect begin\n"
                               "module sealed; endmodule\n"
                               "`pragma protect end\n"
                               "module clear; endmodule\n"
                               "module t; sealed s(); clear c(); endmodule\n",
                               kInstanceKey),
              kInstanceKey, f_);
  EXPECT_EQ(vpi_get(vpiProtected, By("t.s")), 1);
  EXPECT_EQ(vpi_get(vpiProtected, By("t.c")), 0);
}

TEST_F(InstanceItemsOfARun, PackageAndUnitObjectsAreInsideNoModule) {
  Run("int g;\n"
      "package pk; int v; endpackage\n"
      "module top; int x; endmodule\n");
  vpiHandle v = Named(vpiVariables, By("pk"), "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(vpi_handle(vpiModule, v), nullptr);
  vpiHandle g = Named(vpiVariables, Unit(), "g");
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(vpi_handle(vpiModule, g), nullptr);
}

TEST_F(InstanceItemsOfARun, InterfacesAndProgramsReachOnlyTheirTypedefs) {
  Run("package pk; typedef int pk_t; endpackage\n"
      "interface ifc; import pk::*; typedef logic i_t; pk_t a; endinterface\n"
      "program prg; typedef logic p_t; pk::pk_t b; endprogram\n"
      "module top; import pk::pk_t; typedef bit m_t; pk_t c;\n"
      "  ifc i0(); prg p0(); endmodule\n");
  EXPECT_EQ(NamesOf(vpiTypedef, By("top.i0")), std::vector<std::string>{"i_t"});
  EXPECT_EQ(NamesOf(vpiTypedef, By("top.p0")), std::vector<std::string>{"p_t"});
  EXPECT_EQ(NamesOf(vpiTypedef, By("top")), std::vector<std::string>{"m_t"});
  EXPECT_EQ(NamesOf(vpiTypedef, By("pk")), std::vector<std::string>{"pk_t"});
}

TEST_F(InstanceItemsOfARun, ADotFollowsAComponentBelowAPackageOrTheUnit) {
  Run("task ut; int v; endtask\n"
      "class UC; function void m(); endfunction endclass\n"
      "package pkg;\n"
      "  task t; int v; endtask\n"
      "  class C; function void m(); endfunction endclass\n"
      "endpackage\n"
      "module top; endmodule\n");
  struct Scope {
    vpiHandle pkg;
    const char* task;
    const char* cls;
    const char* prefix;
  };
  for (const Scope& s : {Scope{By("pkg"), "t", "C", "pkg::"},
                         Scope{Unit(), "ut", "UC", "$unit::"}}) {
    ASSERT_NE(s.pkg, nullptr) << s.prefix;
    vpiHandle t = Named(vpiTaskFunc, s.pkg, s.task);
    ASSERT_NE(t, nullptr) << s.prefix;
    EXPECT_EQ(FullNameOfChild(t, "v"), std::string(s.prefix) + s.task + ".v");
    vpiHandle c = Named(vpiClassDefn, s.pkg, s.cls);
    ASSERT_NE(c, nullptr) << s.prefix;
    vpiHandle m = Named(vpiMethods, c, "m");
    ASSERT_NE(m, nullptr) << s.prefix;
    EXPECT_EQ(std::string(vpi_get_str(vpiFullName, m)),
              std::string(s.prefix) + s.cls + "::m");
  }
}

constexpr const char* kDefinitionsApart =
    "interface ifc;\n"
    "  timeunit 1us; timeprecision 10ns;\n"
    "endinterface\n"
    "program prg;\n"
    "  timeunit 100ns; timeprecision 1ns;\n"
    "endprogram\n"
    "package pk;\n"
    "  timeunit 10us; timeprecision 100ps;\n"
    "  int v;\n"
    "endpackage\n"
    "module top;\n"
    "  timeunit 1ns; timeprecision 1ps;\n"
    "  ifc i0();\n"
    "  prg p0();\n"
    "endmodule\n";

TEST_F(InstanceItemsOfARun, InterfacesAndProgramsHaveTheirDefinitionsLine) {
  Run(kDefinitionsApart);
  EXPECT_EQ(vpi_get(vpiDefLineNo, By("top.i0")), 1);
  EXPECT_EQ(vpi_get(vpiDefLineNo, By("top.p0")), 4);
  for (const char* name : {"top.i0", "top.p0"}) {
    EXPECT_STREQ(vpi_get_str(vpiDefFile, By(name)), "<test>") << name;
  }
}

TEST_F(InstanceItemsOfARun, InterfacesAndProgramsHaveTheirTimescale) {
  Run(kDefinitionsApart);
  EXPECT_EQ(vpi_get(vpiTimeUnit, By("top.i0")), -6);
  EXPECT_EQ(vpi_get(vpiTimePrecision, By("top.i0")), -8);
  EXPECT_EQ(vpi_get(vpiTimeUnit, By("top.p0")), -7);
  EXPECT_EQ(vpi_get(vpiTimePrecision, By("top.p0")), -9);
}

TEST_F(InstanceItemsOfARun, DISABLED_APackageHasItsDefinitionsLineAndFile) {
  Run(kDefinitionsApart);
  EXPECT_EQ(vpi_get(vpiDefLineNo, By("pk")), 7);
  EXPECT_STREQ(vpi_get_str(vpiDefFile, By("pk")), "<test>");
}

TEST_F(InstanceItemsOfARun, DISABLED_APackageHasItsTimescale) {
  Run(kDefinitionsApart);
  EXPECT_EQ(vpi_get(vpiTimeUnit, By("pk")), -5);
  EXPECT_EQ(vpi_get(vpiTimePrecision, By("pk")), -10);
}

TEST_F(InstanceItemsOfARun, AWildcardImportedItemIsNotReachedThroughIt) {
  Run("package pkg; parameter int P = 42; endpackage\n"
      "module top; import pkg::*; int x = P; endmodule\n");
  EXPECT_EQ(vpi_handle_by_name(VpiText("top.P"), nullptr), nullptr);
}

TEST_F(InstanceItemsOfARun, EveryObjectReachesItsImmediateInstance) {
  Run("package pk; int pv; endpackage\n"
      "interface ifc; int iv; endinterface\n"
      "program prg; int qv; endprogram\n"
      "module sub; int sv; endmodule\n"
      "module top; sub m1(); ifc i0(); prg p0(); endmodule\n");
  struct Case {
    const char* scope;
    const char* item;
  };
  for (const Case& c : {Case{"top.m1", "sv"}, Case{"top.i0", "iv"},
                        Case{"top.p0", "qv"}, Case{"pk", "pv"}}) {
    vpiHandle scope = By(c.scope);
    vpiHandle item = Named(vpiVariables, scope, c.item);
    ASSERT_NE(item, nullptr) << c.item;
    EXPECT_EQ(VpiObjectOf(InstanceOf(item)), VpiObjectOf(scope)) << c.item;
  }
}

}  // namespace
}  // namespace delta
