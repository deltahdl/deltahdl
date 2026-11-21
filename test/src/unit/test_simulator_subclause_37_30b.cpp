#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

using Facts = std::vector<std::string>;

class InterfaceTypespecsInEveryPlace : public VpiDesignRun {
 protected:
  static vpiHandle Through(int relation, vpiHandle ref) {
    return ref == nullptr ? nullptr : vpi_handle(relation, ref);
  }

  static std::string Text(int property, vpiHandle obj) {
    const char* text = vpi_get_str(property, obj);
    return text == nullptr ? "-" : text;
  }

  static std::string AssignedBy(vpiHandle assign, vpiHandle typespec) {
    vpiHandle rhs = vpi_handle(vpiRhs, assign);
    std::string facts = " " + Text(vpiName, vpi_handle(vpiLhs, assign)) + "=";
    if (rhs == nullptr) {
      facts += "-";
    } else if (vpi_get(vpiType, rhs) == vpiConstant) {
      facts += std::to_string(IntegerOf(rhs));
    } else {
      facts += Text(vpiType, rhs);
    }
    if (VpiObjectOf(Through(vpiInterfaceTypespec, assign)) !=
        VpiObjectOf(typespec)) {
      facts += "(of another typespec)";
    }
    return facts;
  }

  static std::string FactsOf(vpiHandle typespec) {
    if (typespec == nullptr) return "none";
    std::string facts =
        Text(vpiType, typespec) + " " + Text(vpiName, typespec) + " ";
    if (vpi_get(vpiType, typespec) == vpiArrayTypespec) {
      return facts + "of " + FactsOf(vpi_handle(vpiElemTypespec, typespec));
    }
    facts += Text(vpiDefName, typespec) +
             " modport=" + std::to_string(vpi_get(vpiIsModPort, typespec));
    for (vpiHandle assign : ObjectsOf(vpiParamAssign, typespec)) {
      facts += AssignedBy(assign, typespec);
    }
    vpiHandle parent = vpi_handle(vpiParent, typespec);
    if (parent != nullptr) facts += " parent{" + FactsOf(parent) + "}";
    return facts;
  }

  static Facts TypedefFacts(vpiHandle scope, const Facts& names) {
    Facts facts;
    for (const std::string& name : names) {
      facts.push_back(
          FactsOf(scope == nullptr ? nullptr : Named(vpiTypedef, scope, name)));
    }
    return facts;
  }

  static Facts VarFacts(const std::vector<vpiHandle>& vars) {
    Facts facts;
    for (vpiHandle var : vars) {
      facts.push_back(FactsOf(Through(vpiTypespec, var)));
    }
    return facts;
  }

  static vpiHandle Tf(const char* name) {
    return Named(vpiTaskFunc, By("top"), name);
  }

  static vpiHandle Formal(const char* tf, const char* name) {
    vpiHandle scope = Tf(tf);
    return scope == nullptr ? nullptr
                            : Through(vpiExpr, Named(vpiIODecl, scope, name));
  }

  static vpiHandle Local(vpiHandle scope, const char* name) {
    return scope == nullptr ? nullptr
                            : Named(vpiVirtualInterfaceVar, scope, name);
  }

  static vpiHandle Defn() { return Named(vpiClassDefn, By("top"), "C"); }

  static vpiHandle Unit() {
    for (vpiHandle package : ObjectsOf(vpiPackage, nullptr)) {
      if (vpi_get(vpiUnit, package) == 1) return package;
    }
    return nullptr;
  }
};

constexpr const char* kEveryPlace =
    "interface SBus #(parameter WIDTH = 8, parameter type T = logic);\n"
    "  logic req, grant;\n"
    "  logic [WIDTH-1:0] addr, data;\n"
    "  modport phy(input addr, inout data);\n"
    "endinterface\n"
    "interface P;\n"
    "  logic a;\n"
    "  modport m(input a);\n"
    "endinterface\n"
    "package pk;\n"
    "  typedef virtual SBus#(7) vp_t;\n"
    "  typedef virtual SBus.phy vpp_t;\n"
    "  typedef virtual SBus#(9).phy vpm_t [1:2];\n"
    "endpackage\n"
    "typedef virtual SBus#(3) vu_t;\n"
    "typedef virtual SBus.phy vup_t;\n"
    "typedef virtual SBus#(5).phy vum_t [1:2];\n"
    "interface I;\n"
    "  typedef virtual SBus#(21) it;\n"
    "  typedef virtual SBus.phy itp;\n"
    "  typedef virtual SBus#(22).phy itm [1:2];\n"
    "endinterface\n"
    "program prg;\n"
    "  typedef virtual SBus#(12) pg_t;\n"
    "  typedef virtual SBus.phy pgp_t;\n"
    "  typedef virtual SBus#(10).phy pgm_t [1:2];\n"
    "  virtual SBus.phy pgv;\n"
    "endprogram\n"
    "module top;\n"
    "  typedef virtual SBus.phy SBp;\n"
    "  typedef virtual SBus#(16).phy SBp16;\n"
    "  typedef virtual SBus#(.WIDTH(16)) SBw;\n"
    "  typedef virtual SBus#(16, byte) SBo;\n"
    "  typedef virtual P pt;\n"
    "  typedef virtual SBus#(32).phy SBphy [1:4];\n"
    "  virtual SBus v;\n"
    "  virtual SBus#(16) v16;\n"
    "  virtual SBus.phy vp;\n"
    "  virtual P.m pm;\n"
    "  vu_t vu;\n"
    "  vup_t vup;\n"
    "  vum_t vum;\n"
    "  class C;\n"
    "    virtual SBus cv;\n"
    "    virtual SBus.phy cp;\n"
    "    static virtual SBus#(16) cs;\n"
    "    typedef virtual SBus#(6) cv_t;\n"
    "    typedef virtual SBus.phy cp_t;\n"
    "    typedef virtual SBus#(11).phy cm_t [1:2];\n"
    "  endclass\n"
    "  C c = new;\n"
    "  task automatic t(virtual SBus tb, virtual SBus.phy tp);\n"
    "    typedef virtual SBus#(13) tt;\n"
    "    typedef virtual SBus.phy ttp;\n"
    "    typedef virtual SBus#(17).phy ttm [1:2];\n"
    "    virtual SBus#(16) tl;\n"
    "  endtask\n"
    "  function void f(virtual SBus.phy fp);\n"
    "    typedef virtual SBus#(18) ftw;\n"
    "    typedef virtual SBus.phy ft;\n"
    "    typedef virtual SBus#(19).phy ftm [1:2];\n"
    "    virtual SBus fl;\n"
    "  endfunction\n"
    "  if (1) begin : g\n"
    "    typedef virtual SBus#(14) gt;\n"
    "    typedef virtual SBus.phy gp_t;\n"
    "    typedef virtual SBus#(15).phy gm_t [1:2];\n"
    "    virtual SBus.phy gv;\n"
    "  end\n"
    "  initial begin : blk\n"
    "    typedef virtual SBus#(15) bt;\n"
    "    typedef virtual SBus.phy btp;\n"
    "    typedef virtual SBus#(20).phy btm [1:2];\n"
    "    virtual SBus.phy x;\n"
    "  end\n"
    "  SBus #(16) bus();\n"
    "  prg pi();\n"
    "  I ii();\n"
    "endmodule\n";

std::string Phy(const std::string& name, const std::string& assigned) {
  return "vpiInterfaceTypespec " + name +
         " phy modport=1 parent{vpiInterfaceTypespec - SBus modport=0" +
         assigned + "}";
}

std::string Whole(const std::string& name, const std::string& assigned) {
  return "vpiInterfaceTypespec " + name + " SBus modport=0" + assigned;
}

std::string PhyArray(const std::string& name, const std::string& assigned) {
  return "vpiArrayTypespec " + name + " of " + Phy("-", assigned);
}

TEST_F(InterfaceTypespecsInEveryPlace, AModuleTypedefIsItsInterfaceTypespec) {
  Run(kEveryPlace);
  EXPECT_EQ(
      TypedefFacts(By("top"), {"SBp", "SBp16", "SBw", "SBo", "pt", "SBphy"}),
      (Facts{Phy("SBp", ""), Phy("SBp16", " WIDTH=16"),
             Whole("SBw", " WIDTH=16"),
             Whole("SBo", " WIDTH=16 T=vpiByteTypespec"),
             "vpiInterfaceTypespec pt P modport=0",
             PhyArray("SBphy", " WIDTH=32")}));
}

TEST_F(InterfaceTypespecsInEveryPlace, APackageTypedefIsItsInterfaceTypespec) {
  Run(kEveryPlace);
  EXPECT_EQ(TypedefFacts(By("pk"), {"vp_t", "vpp_t", "vpm_t"}),
            (Facts{Whole("vp_t", " WIDTH=7"), Phy("vpp_t", ""),
                   PhyArray("vpm_t", " WIDTH=9")}));
}

TEST_F(InterfaceTypespecsInEveryPlace, AClassTypedefIsItsInterfaceTypespec) {
  Run(kEveryPlace);
  EXPECT_EQ(TypedefFacts(Defn(), {"cv_t", "cp_t", "cm_t"}),
            (Facts{Whole("cv_t", " WIDTH=6"), Phy("cp_t", ""),
                   PhyArray("cm_t", " WIDTH=11")}));
}

TEST_F(InterfaceTypespecsInEveryPlace,
       AGenerateBlockTypedefIsItsInterfaceTypespec) {
  Run(kEveryPlace);
  EXPECT_EQ(TypedefFacts(By("top.g"), {"gt", "gp_t", "gm_t"}),
            (Facts{Whole("gt", " WIDTH=14"), Phy("gp_t", ""),
                   PhyArray("gm_t", " WIDTH=15")}));
}

TEST_F(InterfaceTypespecsInEveryPlace, AProgramTypedefIsItsInterfaceTypespec) {
  Run(kEveryPlace);
  EXPECT_EQ(TypedefFacts(By("top.pi"), {"pg_t", "pgp_t", "pgm_t"}),
            (Facts{Whole("pg_t", " WIDTH=12"), Phy("pgp_t", ""),
                   PhyArray("pgm_t", " WIDTH=10")}));
}

TEST_F(InterfaceTypespecsInEveryPlace,
       AnInterfaceTypedefIsItsInterfaceTypespec) {
  Run(kEveryPlace);
  EXPECT_EQ(TypedefFacts(By("top.ii"), {"it", "itp", "itm"}),
            (Facts{Whole("it", " WIDTH=21"), Phy("itp", ""),
                   PhyArray("itm", " WIDTH=22")}));
}

TEST_F(InterfaceTypespecsInEveryPlace,
       ACompilationUnitTypedefIsItsInterfaceTypespec) {
  Run(kEveryPlace);
  EXPECT_EQ(TypedefFacts(Unit(), {"vu_t", "vup_t", "vum_t"}),
            (Facts{Whole("vu_t", " WIDTH=3"), Phy("vup_t", ""),
                   PhyArray("vum_t", " WIDTH=5")}));
}

TEST_F(InterfaceTypespecsInEveryPlace,
       AVarOfACompilationUnitTypedefReachesItsInterfaceTypespec) {
  Run(kEveryPlace);
  EXPECT_EQ(VarFacts({By("top.vu"), By("top.vup")}),
            (Facts{Whole("vu_t", " WIDTH=3"), Phy("vup_t", "")}));
  EXPECT_EQ(
      FactsOf(Through(vpiElemTypespec, Through(vpiTypespec, By("top.vum")))),
      Phy("-", " WIDTH=5"));
}

TEST_F(InterfaceTypespecsInEveryPlace,
       DISABLED_ASubroutineOrBlockTypedefIsItsInterfaceTypespec) {
  Run(kEveryPlace);
  EXPECT_EQ(TypedefFacts(Tf("t"), {"tt", "ttp", "ttm"}),
            (Facts{Whole("tt", " WIDTH=13"), Phy("ttp", ""),
                   PhyArray("ttm", " WIDTH=17")}));
  EXPECT_EQ(TypedefFacts(Tf("f"), {"ftw", "ft", "ftm"}),
            (Facts{Whole("ftw", " WIDTH=18"), Phy("ft", ""),
                   PhyArray("ftm", " WIDTH=19")}));
  EXPECT_EQ(TypedefFacts(By("top.blk"), {"bt", "btp", "btm"}),
            (Facts{Whole("bt", " WIDTH=15"), Phy("btp", ""),
                   PhyArray("btm", " WIDTH=20")}));
}

TEST_F(InterfaceTypespecsInEveryPlace, AModuleVarReachesItsInterfaceTypespec) {
  Run(kEveryPlace);
  EXPECT_EQ(VarFacts({By("top.v"), By("top.v16"), By("top.vp"), By("top.pm")}),
            (Facts{Whole("-", ""), Whole("-", " WIDTH=16"), Phy("-", ""),
                   "vpiInterfaceTypespec - m modport=1"
                   " parent{vpiInterfaceTypespec - P modport=0}"}));
}

TEST_F(InterfaceTypespecsInEveryPlace,
       AProgramOrGenerateBlockVarReachesItsInterfaceTypespec) {
  Run(kEveryPlace);
  EXPECT_EQ(VarFacts({By("top.pi.pgv"), By("top.g.gv")}),
            (Facts{Phy("-", ""), Phy("-", "")}));
}

TEST_F(InterfaceTypespecsInEveryPlace,
       AClassPropertyOfTheDefnReachesItsInterfaceTypespec) {
  Run(kEveryPlace);
  vpiHandle defn = Defn();
  ASSERT_NE(defn, nullptr);
  EXPECT_EQ(VarFacts({Named(vpiVariables, defn, "cv"),
                      Named(vpiVariables, defn, "cp"),
                      Named(vpiVariables, defn, "cs"), By("top.C::cs")}),
            (Facts{Whole("-", ""), Phy("-", ""), Whole("-", " WIDTH=16"),
                   Whole("-", " WIDTH=16")}));
}

TEST_F(InterfaceTypespecsInEveryPlace,
       DISABLED_AClassPropertyOfAnObjReachesItsInterfaceTypespec) {
  Run(kEveryPlace);
  vpiHandle obj = Through(vpiClassObj, By("top.c"));
  ASSERT_NE(obj, nullptr);
  EXPECT_EQ(VarFacts({Local(obj, "cv"), Local(obj, "cp")}),
            (Facts{Whole("-", ""), Phy("-", "")}));
}

TEST_F(InterfaceTypespecsInEveryPlace,
       DISABLED_ASubroutineOrBlockVarReachesItsInterfaceTypespec) {
  Run(kEveryPlace);
  EXPECT_EQ(
      VarFacts({Formal("t", "tb"), Formal("t", "tp"), Formal("f", "fp"),
                Local(Tf("t"), "tl"), Local(Tf("f"), "fl"), By("top.blk.x")}),
      (Facts{Whole("-", ""), Phy("-", ""), Phy("-", ""),
             Whole("-", " WIDTH=16"), Whole("-", ""), Phy("-", "")}));
}

}  // namespace
}  // namespace delta
