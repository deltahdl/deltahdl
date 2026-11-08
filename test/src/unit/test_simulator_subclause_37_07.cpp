#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class Modport : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(Modport, ReportsItsNameViaVpiName) {
  VpiObject modport;
  modport.type = vpiModport;
  modport.name = "phy";

  EXPECT_STREQ(vpi_get_str(vpiName, VpiHandleOf(&modport)), "phy");
}

TEST_F(Modport, InterfaceAndModportTraverseBothWays) {
  VpiObject iface;
  iface.type = vpiInterface;

  VpiObject modport;
  modport.type = vpiModport;
  modport.name = "phy";
  modport.parent = &iface;
  iface.children = {&modport};

  vpiHandle iter = vpi_iterate(vpiModport, VpiHandleOf(&iface));
  ASSERT_NE(iter, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(iter)), &modport);
  EXPECT_EQ(vpi_scan(iter), nullptr);

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInterface, VpiHandleOf(&modport))),
            &iface);
}

TEST_F(Modport, ModportAndIoDeclTraverseBothWays) {
  VpiObject modport;
  modport.type = vpiModport;

  VpiObject in_decl;
  in_decl.type = vpiIODecl;
  in_decl.parent = &modport;
  VpiObject out_decl;
  out_decl.type = vpiIODecl;
  out_decl.parent = &modport;
  modport.children = {&in_decl, &out_decl};

  vpiHandle iter = vpi_iterate(vpiIODecl, VpiHandleOf(&modport));
  ASSERT_NE(iter, nullptr);
  int count = 0;
  while (vpi_scan(iter) != nullptr) ++count;
  EXPECT_EQ(count, 2);

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModport, VpiHandleOf(&in_decl))),
            &modport);
}

TEST_F(Modport, ModportWithNoIoDeclsIteratesToNone) {
  VpiObject modport;
  modport.type = vpiModport;

  EXPECT_EQ(vpi_iterate(vpiIODecl, VpiHandleOf(&modport)), nullptr);
}

TEST_F(Modport, ModportWithoutEnclosingInterfaceReachesNone) {
  VpiObject modport;
  modport.type = vpiModport;

  EXPECT_EQ(vpi_handle(vpiInterface, VpiHandleOf(&modport)), nullptr);
}

TEST_F(Modport, InterfaceWithNoModportsIteratesToNone) {
  VpiObject iface;
  iface.type = vpiInterface;

  EXPECT_EQ(vpi_iterate(vpiModport, VpiHandleOf(&iface)), nullptr);
}

TEST_F(Modport, IoDeclWithoutEnclosingModportReachesNone) {
  VpiObject io_decl;
  io_decl.type = vpiIODecl;

  EXPECT_EQ(vpi_handle(vpiModport, VpiHandleOf(&io_decl)), nullptr);
}

class ModportsOfARun : public VpiDesignRun {
 protected:
  static constexpr const char* kTwoModports =
      "interface ifc; logic a, b;\n"
      "  modport mp(input a, output b);\n"
      "  modport mq(input b);\n"
      "endinterface\n"
      "module top; ifc i0(); endmodule\n";

  static std::vector<std::string> ScannedNames(int type, vpiHandle ref) {
    std::vector<std::string> names;
    vpiHandle it = vpi_iterate(type, ref);
    if (it == nullptr) return names;
    while (vpiHandle obj = vpi_scan(it)) {
      names.emplace_back(vpi_get_str(vpiName, obj));
    }
    return names;
  }

  static vpiHandle Instance() {
    return vpi_handle_by_name(VpiText("top.i0"), nullptr);
  }
};

TEST_F(ModportsOfARun, AnInterfaceInstanceIteratesItsModports) {
  Run(kTwoModports);
  EXPECT_EQ(ScannedNames(vpiModport, Instance()),
            (std::vector<std::string>{"mp", "mq"}));
}

TEST_F(ModportsOfARun, AModportReachesItsInterfaceInstance) {
  Run(kTwoModports);
  vpiHandle mp = Named(vpiModport, Instance(), "mp");
  ASSERT_NE(mp, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInterface, mp)), VpiObjectOf(Instance()));
}

TEST_F(ModportsOfARun, AModportIteratesItsIoDecls) {
  Run(kTwoModports);
  EXPECT_EQ(ScannedNames(vpiIODecl, Named(vpiModport, Instance(), "mp")),
            (std::vector<std::string>{"a", "b"}));
  EXPECT_EQ(ScannedNames(vpiIODecl, Named(vpiModport, Instance(), "mq")),
            (std::vector<std::string>{"b"}));
}

TEST_F(ModportsOfARun, AnIoDeclReportsItsModportsDirection) {
  Run(kTwoModports);
  vpiHandle mp = Named(vpiModport, Instance(), "mp");
  vpiHandle mq = Named(vpiModport, Instance(), "mq");
  EXPECT_EQ(vpi_get(vpiDirection, Named(vpiIODecl, mp, "a")), vpiInput);
  EXPECT_EQ(vpi_get(vpiDirection, Named(vpiIODecl, mp, "b")), vpiOutput);
  EXPECT_EQ(vpi_get(vpiDirection, Named(vpiIODecl, mq, "b")), vpiInput);
}

TEST_F(ModportsOfARun, AnIoDeclOfARefPortReportsVpiRef) {
  Run("interface ifc; logic a; modport mr(ref a); endinterface\n"
      "module top; ifc i0(); endmodule\n");
  vpiHandle mr = Named(vpiModport, Instance(), "mr");
  EXPECT_EQ(vpi_get(vpiDirection, Named(vpiIODecl, mr, "a")), vpiRef);
}

TEST_F(ModportsOfARun, AnIoDeclOfAnInoutPortReportsVpiInout) {
  Run("interface ifc; wire w; modport mb(inout w); endinterface\n"
      "module top; ifc i0(); endmodule\n");
  vpiHandle mb = Named(vpiModport, Instance(), "mb");
  EXPECT_EQ(vpi_get(vpiDirection, Named(vpiIODecl, mb, "w")), vpiInout);
}

TEST_F(ModportsOfARun, AModportsClockingBlockIsNoIoDecl) {
  Run("interface ifc; logic a;\n"
      "  extern task put();\n"
      "  task get(); endtask\n"
      "  clocking cb @(posedge a); endclocking\n"
      "  modport mp(input a, import get, export put, clocking cb);\n"
      "endinterface\n"
      "module tgt(ifc.mp b); task b.put(); endtask endmodule\n"
      "module top; ifc i0(); tgt t(i0.mp); endmodule\n");
  EXPECT_EQ(ScannedNames(vpiIODecl, Named(vpiModport, Instance(), "mp")),
            (std::vector<std::string>{"a", "get", "put"}));
}

TEST_F(ModportsOfARun, AnIoDeclReachesItsModport) {
  Run(kTwoModports);
  vpiHandle mq = Named(vpiModport, Instance(), "mq");
  ASSERT_NE(mq, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModport, Named(vpiIODecl, mq, "b"))),
            VpiObjectOf(mq));
}

TEST_F(ModportsOfARun, AModuleInstanceHasNoModports) {
  Run(kTwoModports);
  EXPECT_EQ(
      vpi_iterate(vpiModport, vpi_handle_by_name(VpiText("top"), nullptr)),
      nullptr);
}

}  // namespace
}  // namespace delta
