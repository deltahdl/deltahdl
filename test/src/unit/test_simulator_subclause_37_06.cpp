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

class Interface : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(Interface, IndexTransitionReachesArrayIndex) {
  VpiObject index_expr;
  index_expr.type = vpiConstant;

  VpiObject member;
  member.type = vpiInterface;
  member.array_member = true;
  member.index_expr = &index_expr;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiIndex, VpiHandleOf(&member))),
            &index_expr);
}

TEST_F(Interface, IndexTransitionIsNullWhenNotAnArrayElement) {
  VpiObject stray_expr;
  stray_expr.type = vpiConstant;

  VpiObject standalone;
  standalone.type = vpiInterface;
  standalone.array_member = false;
  standalone.index_expr = &stray_expr;
  standalone.children.push_back(&stray_expr);

  EXPECT_EQ(vpi_handle(vpiIndex, VpiHandleOf(&standalone)), nullptr);
}

TEST_F(Interface, IndexTransitionIsNullForArrayElementWithoutIndexExpr) {
  VpiObject child_expr;
  child_expr.type = vpiConstant;

  VpiObject member;
  member.type = vpiInterface;
  member.array_member = true;
  member.index_expr = nullptr;
  member.children.push_back(&child_expr);

  EXPECT_EQ(vpi_handle(vpiIndex, VpiHandleOf(&member)), nullptr);
}

class InterfacesOfARun : public VpiDesignRun {};

constexpr const char* kInterfaceInstance =
    "interface ifc; logic d; endinterface\n"
    "module top; ifc i0(); endmodule\n";

TEST_F(InterfacesOfARun, AnInterfaceInstanceIsReachedAsAnInterface) {
  Run(kInterfaceInstance);
  EXPECT_EQ(NamesOf(vpiInterface, vpi_handle_by_name(VpiText("top"), nullptr)),
            (std::vector<std::string>{"i0"}));
}

TEST_F(InterfacesOfARun, AnInterfaceInstanceIsOfTypeInterface) {
  Run(kInterfaceInstance);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle_by_name(VpiText("top.i0"), nullptr)),
            vpiInterface);
}

TEST_F(InterfacesOfARun, AnInterfaceInstancesDefinitionIsItsInterface) {
  Run(kInterfaceInstance);
  EXPECT_STREQ(
      vpi_get_str(vpiDefName, vpi_handle_by_name(VpiText("top.i0"), nullptr)),
      "ifc");
}

}  // namespace
}  // namespace delta
