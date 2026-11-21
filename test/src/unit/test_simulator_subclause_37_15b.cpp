#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class RefObjItemsOfARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    Probed().clear();
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$probe");
    data.calltf = &ProbeFormalActual;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
    Run(Design());
  }

  static std::string Design() {
    return "interface simple; wire req; logic gnt; event ev;\n"
           "  modport target (input req, output gnt);\n"
           "  task automatic it(ref int r); r = 1; endtask\n"
           "endinterface\n"
           "package pk;\n"
           "  task automatic pt(ref int r); r = 2; endtask\n"
           "endpackage\n"
           "module child1(simple s); logic x; initial #1 x = s.req; endmodule\n"
           "module child3(simple.target t); endmodule\n"
           "module g3(interface.target t); endmodule\n"
           "module arr(simple s[2]); endmodule\n"
           "module garr(interface s[2]); endmodule\n"
           "module m(ref logic [3:0] r); logic [3:0] y;\n"
           "  initial begin r[0] = 1'b1; y = r; r[1:0] = 2'b10; end\n"
           "endmodule\n"
           "module ev(ref event e, ref event ea[2]); endmodule\n"
           "program p(ref int r); endprogram\n"
           "interface ri(ref int r); endinterface\n"
           "module top; simple i(); simple ia[2](); logic [3:0] a;\n"
           "  int n1, n2, fr; event e1; event ea1[2];\n"
           "  class C; task mt(ref int r); r = 3; endtask endclass\n"
           "  C c;\n"
           "  child1 i1(i); child3 i3(i); g3 u3(i); arr u5(ia); garr u6(ia);\n"
           "  m u1(a); ev u7(e1, ea1); p u8(n1); ri u9(n2);\n"
           "  task automatic t(ref int r); r = r + 1; $probe; endtask\n"
           "  task automatic tb(ref logic [3:0] r); r[0] = 1'b1; endtask\n"
           "  function automatic int f(ref int r); return r; endfunction\n"
           "  initial begin #2 t(n1); t(n2); tb(a); fr = f(n1);\n"
           "    c = new; c.mt(n1); pk::pt(n1); i.it(n1); end\n"
           "endmodule\n";
  }

  static std::vector<VpiObject*>& Probed() {
    static std::vector<VpiObject*> probed;
    return probed;
  }

  static PLI_INT32 ProbeFormalActual(PLI_BYTE8*) {
    Probed().push_back(
        VpiObjectOf(vpi_handle(vpiActual, Formal(Tf("t"), "r"))));
    return 0;
  }

  static vpiHandle Low(const char* inst, const char* name) {
    vpiHandle port = Named(vpiPort, By(inst), name);
    return port == nullptr ? nullptr : vpi_handle(vpiLowConn, port);
  }

  static vpiHandle High(const char* inst, const char* name) {
    vpiHandle port = Named(vpiPort, By(inst), name);
    return port == nullptr ? nullptr : vpi_handle(vpiHighConn, port);
  }

  static vpiHandle Tf(const char* name) {
    return Named(vpiTaskFunc, By("top"), name);
  }

  static vpiHandle Formal(vpiHandle tf, const char* name) {
    vpiHandle io = Named(vpiIODecl, tf, name);
    return io == nullptr ? nullptr : vpi_handle(vpiExpr, io);
  }

  static vpiHandle PackageTf(const char* pkg, const char* name) {
    for (vpiHandle p : ObjectsOf(vpiPackage, nullptr)) {
      const char* own = vpi_get_str(vpiName, p);
      if (own != nullptr && std::string(own) == pkg) {
        return Named(vpiTaskFunc, p, name);
      }
    }
    return nullptr;
  }

  static std::vector<vpiHandle> Stmts(vpiHandle stmt) {
    if (stmt == nullptr) return {};
    const int kKind = vpi_get(vpiType, stmt);
    if (kKind != vpiBegin && kKind != vpiNamedBegin) return {stmt};
    return ObjectsOf(vpiStmt, stmt);
  }

  static std::vector<vpiHandle> ProcessStmts(const char* inst) {
    std::vector<vpiHandle> all;
    for (vpiHandle proc : ObjectsOf(vpiProcess, By(inst))) {
      for (vpiHandle stmt : Stmts(vpi_handle(vpiStmt, proc))) {
        all.push_back(stmt);
      }
    }
    return all;
  }

  static vpiHandle Side(int side, const std::vector<vpiHandle>& stmts,
                        std::size_t place) {
    if (place >= stmts.size()) return nullptr;
    vpiHandle stmt = stmts[place];
    if (vpi_get(vpiType, stmt) == vpiDelayControl) {
      stmt = vpi_handle(vpiStmt, stmt);
    }
    return stmt == nullptr ? nullptr : vpi_handle(side, stmt);
  }

  static vpiHandle InTask(int side, const char* tf, std::size_t place) {
    return Side(side, Stmts(vpi_handle(vpiStmt, Tf(tf))), place);
  }

  static bool Same(vpiHandle a, vpiHandle b) {
    return a != nullptr && VpiObjectOf(a) == VpiObjectOf(b);
  }

  static int KindOf(vpiHandle obj) {
    return obj == nullptr ? 0 : vpi_get(vpiType, obj);
  }

  static std::string FullNameOf(vpiHandle obj) {
    const char* name = obj == nullptr ? nullptr : vpi_get_str(vpiFullName, obj);
    return name == nullptr ? "" : name;
  }
};

TEST_F(RefObjItemsOfARun, NamedEventAndEventArrayPortsLowConnsAreRefObjs) {
  EXPECT_EQ(KindOf(Low("top.u7", "e")), vpiRefObj);
  EXPECT_EQ(KindOf(Low("top.u7", "ea")), vpiRefObj);
}

TEST_F(RefObjItemsOfARun, AnEventPortsActualIsTheEventItIsBoundTo) {
  EXPECT_TRUE(Same(vpi_handle(vpiActual, Low("top.u7", "e")), By("top.e1")));
  vpiHandle array = vpi_handle(vpiActual, Low("top.u7", "ea"));
  EXPECT_EQ(KindOf(array), vpiNamedEventArray);
  EXPECT_EQ(FullNameOf(array), "top.ea1");
}

TEST_F(RefObjItemsOfARun, AnInterfaceArrayPortsLowConnIsARefObj) {
  EXPECT_EQ(KindOf(Low("top.u5", "s")), vpiRefObj);
  EXPECT_EQ(KindOf(Low("top.u6", "s")), vpiRefObj);
}

TEST_F(RefObjItemsOfARun, DISABLED_AWholeInterfaceArrayIsTheActual) {
  vpiHandle actual = vpi_handle(vpiActual, Low("top.u5", "s"));
  EXPECT_EQ(KindOf(actual), vpiInterfaceArray);
  EXPECT_EQ(FullNameOf(actual), "top.ia");
}

TEST_F(RefObjItemsOfARun, DISABLED_ARefPortsSubelementInTheBodyIsARefObj) {
  std::vector<vpiHandle> stmts = ProcessStmts("top.u1");
  vpiHandle bit = Side(vpiLhs, stmts, 0);
  EXPECT_EQ(KindOf(bit), vpiRefObj);
  EXPECT_TRUE(Same(vpi_handle(vpiParent, bit), Low("top.u1", "r")));
  vpiHandle a0 = vpi_handle(vpiActual, bit);
  EXPECT_EQ(KindOf(a0), vpiVarBit);
  EXPECT_EQ(FullNameOf(a0), "top.a[0]");
}

TEST_F(RefObjItemsOfARun,
       DISABLED_AWholeRefPortInTheBodyIsARefObjBoundToItsActual) {
  vpiHandle whole = Side(vpiRhs, ProcessStmts("top.u1"), 1);
  EXPECT_EQ(KindOf(whole), vpiRefObj);
  EXPECT_TRUE(Same(vpi_handle(vpiActual, whole), By("top.a")));
}

TEST_F(RefObjItemsOfARun,
       DISABLED_ARefObjOfAPartSelectHasThatPartSelectsTypespec) {
  vpiHandle part = Side(vpiLhs, ProcessStmts("top.u1"), 2);
  EXPECT_EQ(KindOf(part), vpiRefObj);
  EXPECT_EQ(KindOf(vpi_handle(vpiActual, part)), vpiPartSelect);
  EXPECT_NE(vpi_handle(vpiTypespec, part), nullptr);
}

TEST_F(RefObjItemsOfARun,
       DISABLED_AnInterfaceMemberThroughAPortIsARefObjOfTheNet) {
  vpiHandle member = Side(vpiRhs, ProcessStmts("top.i1"), 0);
  EXPECT_EQ(KindOf(member), vpiRefObj);
  vpiHandle net = Named(vpiNet, By("top.i"), "req");
  ASSERT_NE(net, nullptr);
  EXPECT_TRUE(Same(vpi_handle(vpiActual, member), net));
  vpiHandle typespec = vpi_handle(vpiTypespec, member);
  EXPECT_NE(typespec, nullptr);
  EXPECT_TRUE(Same(typespec, vpi_handle(vpiTypespec, net)));
}

TEST_F(RefObjItemsOfARun, DISABLED_ATaskFormalsUseInTheBodyIsItsRefObj) {
  vpiHandle formal = Formal(Tf("t"), "r");
  EXPECT_EQ(KindOf(formal), vpiRefObj);
  vpiHandle lhs = InTask(vpiLhs, "t", 0);
  EXPECT_EQ(KindOf(lhs), vpiRefObj);
  EXPECT_TRUE(Same(lhs, formal));
}

TEST_F(RefObjItemsOfARun,
       DISABLED_ATaskFormalsSubelementIsARefObjUnderTheFormal) {
  vpiHandle bit = InTask(vpiLhs, "tb", 0);
  EXPECT_EQ(KindOf(bit), vpiRefObj);
  EXPECT_TRUE(Same(vpi_handle(vpiParent, bit), Formal(Tf("tb"), "r")));
}

TEST_F(RefObjItemsOfARun, EveryKindOfSubroutinesRefFormalIsARefObj) {
  EXPECT_EQ(KindOf(Formal(Tf("f"), "r")), vpiRefObj);
  EXPECT_EQ(
      KindOf(Formal(
          Named(vpiTaskFunc, Named(vpiClassDefn, By("top"), "C"), "mt"), "r")),
      vpiRefObj);
  EXPECT_EQ(KindOf(Formal(PackageTf("pk", "pt"), "r")), vpiRefObj);
  EXPECT_EQ(KindOf(Formal(Named(vpiTaskFunc, By("top.i"), "it"), "r")),
            vpiRefObj);
}

TEST_F(RefObjItemsOfARun, ProgramAndInterfaceRefPortsLowConnsAreRefObjs) {
  vpiHandle prog = Low("top.u8", "r");
  EXPECT_EQ(KindOf(prog), vpiRefObj);
  EXPECT_TRUE(Same(vpi_handle(vpiActual, prog), By("top.n1")));
  vpiHandle ifc = Low("top.u9", "r");
  EXPECT_EQ(KindOf(ifc), vpiRefObj);
  EXPECT_TRUE(Same(vpi_handle(vpiActual, ifc), By("top.n2")));
}

TEST_F(RefObjItemsOfARun, DISABLED_AFormalsActualIsTheArgumentOfTheActiveCall) {
  std::vector<VpiObject*> expected{VpiObjectOf(By("top.n1")),
                                   VpiObjectOf(By("top.n2"))};
  EXPECT_EQ(Probed(), expected);
}

TEST_F(RefObjItemsOfARun, TheNamesFollowTheInstanceWhileTheActualStays) {
  vpiHandle low = Low("top.i1", "s");
  vpiHandle high = High("top.i1", "s");
  EXPECT_STREQ(vpi_get_str(vpiName, low), "s");
  EXPECT_EQ(FullNameOf(low), "top.i1.s");
  EXPECT_STREQ(vpi_get_str(vpiName, high), "i");
  EXPECT_EQ(FullNameOf(high), "top.i");
  EXPECT_TRUE(Same(vpi_handle(vpiActual, low), vpi_handle(vpiActual, high)));
}

TEST_F(RefObjItemsOfARun, DISABLED_APortsRefObjReachesThatPort) {
  EXPECT_TRUE(Same(vpi_handle(vpiPort, Low("top.i1", "s")),
                   Named(vpiPort, By("top.i1"), "s")));
}

TEST_F(RefObjItemsOfARun, APortsRefObjsReachTheInstanceHoldingThem) {
  EXPECT_TRUE(Same(vpi_handle(vpiInstance, Low("top.i1", "s")), By("top.i1")));
  EXPECT_TRUE(Same(vpi_handle(vpiInstance, High("top.i1", "s")), By("top")));
}

TEST_F(RefObjItemsOfARun, DISABLED_AFormalsRefObjReachesItsTaskOrFunction) {
  EXPECT_TRUE(Same(vpi_handle(vpiTaskFunc, Formal(Tf("t"), "r")), Tf("t")));
  EXPECT_TRUE(Same(vpi_handle(vpiTaskFunc, Formal(Tf("f"), "r")), Tf("f")));
}

TEST_F(RefObjItemsOfARun, APortsRefObjReachesNoTaskOrFunction) {
  EXPECT_EQ(vpi_handle(vpiTaskFunc, Low("top.i1", "s")), nullptr);
}

TEST_F(RefObjItemsOfARun, DISABLED_VpiGenericOfInterfaceArrayAndModportPorts) {
  EXPECT_EQ(vpi_get(vpiGeneric, Low("top.u5", "s")), 0);
  EXPECT_EQ(vpi_get(vpiGeneric, Low("top.u6", "s")), 1);
  EXPECT_EQ(vpi_get(vpiGeneric, Low("top.i3", "t")), 0);
  EXPECT_EQ(vpi_get(vpiGeneric, Low("top.u3", "t")), 1);
}

TEST_F(RefObjItemsOfARun, VpiGenericOfARefFormalIsUndefined) {
  EXPECT_EQ(vpi_get(vpiGeneric, Formal(Tf("t"), "r")), vpiUndefined);
}

TEST_F(RefObjItemsOfARun,
       DISABLED_VpiDefNameOfAnInterfaceArrayActualIsTheInterface) {
  EXPECT_STREQ(vpi_get_str(vpiDefName, Low("top.u5", "s")), "simple");
}

TEST_F(RefObjItemsOfARun, VpiDefNameOfADeclaredModportIsThatModport) {
  EXPECT_STREQ(vpi_get_str(vpiDefName, Low("top.i3", "t")), "target");
}

TEST_F(RefObjItemsOfARun, VpiDefNameOfAVariableActualIsNull) {
  EXPECT_EQ(vpi_get_str(vpiDefName, Low("top.u1", "r")), nullptr);
}

TEST_F(RefObjItemsOfARun, OtherActualsHaveNoTypespec) {
  EXPECT_EQ(vpi_handle(vpiTypespec, Low("top.i3", "t")), nullptr);
  EXPECT_EQ(vpi_handle(vpiTypespec, Low("top.u5", "s")), nullptr);
  EXPECT_EQ(vpi_handle(vpiTypespec, Low("top.u7", "e")), nullptr);
  EXPECT_EQ(vpi_handle(vpiTypespec, Low("top.u7", "ea")), nullptr);
}

}  // namespace
}  // namespace delta
