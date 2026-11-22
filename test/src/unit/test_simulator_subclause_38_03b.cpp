#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

std::vector<vpiHandle> held;
std::vector<int> compared;

std::vector<vpiHandle> ArgumentsOfThisCall() {
  std::vector<vpiHandle> args;
  vpiHandle it = vpi_iterate(vpiArgument, vpi_handle(vpiSysTfCall, nullptr));
  if (it == nullptr) return args;
  while (vpiHandle arg = vpi_scan(it)) args.push_back(arg);
  return args;
}

vpiHandle FirstElementOf(const char* array) {
  vpiHandle it =
      vpi_iterate(vpiReg, vpi_handle_by_name(VpiText(array), nullptr));
  return it == nullptr ? nullptr : vpi_scan(it);
}

PLI_INT32 KeepCalltf(PLI_BYTE8*) {
  held = ArgumentsOfThisCall();
  return 0;
}

PLI_INT32 CompareHeldCalltf(PLI_BYTE8*) {
  compared.push_back(held.size() == 2 ? vpi_compare_objects(held[0], held[1])
                                      : -1);
  return 0;
}

PLI_INT32 CompareHeldWithItselfCalltf(PLI_BYTE8*) {
  compared.push_back(held.empty() ? -1 : vpi_compare_objects(held[0], held[0]));
  return 0;
}

PLI_INT32 CompareHeldWithArgumentCalltf(PLI_BYTE8*) {
  std::vector<vpiHandle> args = ArgumentsOfThisCall();
  compared.push_back(held.empty() || args.empty()
                         ? -1
                         : vpi_compare_objects(held[0], args[0]));
  return 0;
}

PLI_INT32 CompareHeldWithFirstElementCalltf(PLI_BYTE8*) {
  compared.push_back(
      held.empty() ? -1
                   : vpi_compare_objects(held[0], FirstElementOf("top.i")));
  return 0;
}

class HeldHandleComparisons : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    held.clear();
    compared.clear();
    Register("$keep", &KeepCalltf);
    Register("$cmp_held", &CompareHeldCalltf);
    Register("$cmp_self", &CompareHeldWithItselfCalltf);
    Register("$cmp_arg", &CompareHeldWithArgumentCalltf);
    Register("$cmp_first", &CompareHeldWithFirstElementCalltf);
  }

  static void Register(const char* name, PLI_INT32 (*calltf)(PLI_BYTE8*)) {
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText(name);
    data.calltf = calltf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }

  static vpiHandle Found(int type, vpiHandle ref, const char* full_name) {
    for (vpiHandle obj : ObjectsOf(type, ref)) {
      if (std::string(vpi_get_str(vpiFullName, obj)) == full_name) return obj;
    }
    return nullptr;
  }
};

TEST_F(HeldHandleComparisons, ObjectsReachedByTwoRoutesAreOneObject) {
  Run("module sub; endmodule\n"
      "module top; wire [3:0] w; logic [3:0] v; sub u(); initial $noop;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  vpiHandle net = Found(vpiNet, top, "top.w");
  ASSERT_NE(net, nullptr);
  EXPECT_EQ(vpi_compare_objects(net, By("top.w")), 1);
  vpiHandle inst = Found(vpiModule, top, "top.u");
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(vpi_compare_objects(inst, By("top.u")), 1);
  vpiHandle by_index = vpi_handle_by_index(By("top.v"), 2);
  ASSERT_NE(by_index, nullptr);
  ASSERT_NE(By("top.v[2]"), nullptr);
  EXPECT_EQ(vpi_compare_objects(by_index, By("top.v[2]")), 1);
  EXPECT_EQ(vpi_compare_objects(by_index, By("top.v[1]")), 0);
}

TEST_F(HeldHandleComparisons, AHeldVarSelectFollowsItsIndex) {
  Run("module top;\n"
      "  integer i [0:3]; int j;\n"
      "  initial begin\n"
      "    j = 0; $keep(i[j]); i[j] = 5; $cmp_first;\n"
      "    #1 j = 1; i[j] = 6; $cmp_first;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(compared, (std::vector<int>{1, 0}));
}

TEST_F(HeldHandleComparisons, HeldMemberReferencesFollowTheirClassHandles) {
  Run("module top;\n"
      "  class C; int a; endclass\n"
      "  C c, d;\n"
      "  initial begin\n"
      "    c = null; d = null; $keep(c.a, d.a); $cmp_held;\n"
      "    #1 c = new; c.a = 5; $cmp_held;\n"
      "    #1 d = c; d.a = 6; $cmp_held;\n"
      "    #1 c = new; c.a = 7; $cmp_held;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(compared, (std::vector<int>{0, 0, 1, 0}));
}

TEST_F(HeldHandleComparisons, AHandleToNoObjectIsNotItself) {
  Run("module top;\n"
      "  class C; int a; endclass\n"
      "  C c;\n"
      "  initial begin\n"
      "    $keep(c.a); $cmp_self;\n"
      "    c = new; $cmp_self;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(compared, (std::vector<int>{0, 1}));
}

TEST_F(HeldHandleComparisons, AHandleWhoseObjectIsGoneMatchesNothing) {
  Run("module top;\n"
      "  class C; int a; endclass\n"
      "  C c;\n"
      "  initial begin\n"
      "    c = new; $keep(c.a); $cmp_self; $cmp_arg(c.a);\n"
      "    c = null; $cmp_self; $cmp_arg(c.a);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(compared, (std::vector<int>{1, 1, 0, 0}));
}

}  // namespace
}  // namespace delta
