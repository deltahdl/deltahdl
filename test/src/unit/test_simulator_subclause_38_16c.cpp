#include <gtest/gtest.h>

#include <map>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

bool Refused(vpiHandle obj, PLI_UINT32 format, std::vector<PLI_INT32> index,
             PLI_UINT32 num) {
  alignas(8) PLI_BYTE8 buffer[256] = {};
  s_vpi_arrayvalue av = {};
  av.format = format;
  av.flags = vpiUserAllocFlag;
  av.value.rawvals = buffer;
  vpi_get_value_array(obj, &av, index.data(), num);
  s_vpi_error_info info = {};
  const PLI_INT32 kLevel = vpi_chk_error(&info);
  return kLevel == vpiError && av.value.rawvals == nullptr;
}

PLI_INT32 FirstInt(vpiHandle obj) {
  PLI_INT32 value = -1;
  PLI_INT32 index = 0;
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.flags = vpiUserAllocFlag;
  av.value.integers = &value;
  vpi_get_value_array(obj, &av, &index, 1);
  return value;
}

class ArrayRefusalsOfARun : public VpiDesignRun {
 protected:
  static bool RefusedByName(const char* name, PLI_UINT32 format) {
    return Refused(By(name), format, {0}, 1);
  }
};

TEST_F(ArrayRefusalsOfARun, EveryFormatTheSectionLeavesOutIsRefused) {
  Run("module top; int ia[2] = '{1, 2}; initial $noop; endmodule\n");
  for (const PLI_UINT32 kFormat :
       {vpiOctStrVal, vpiDecStrVal, vpiHexStrVal, vpiScalarVal, vpiStringVal,
        vpiStrengthVal, vpiObjTypeVal, vpiSuppressVal}) {
    EXPECT_TRUE(RefusedByName("top.ia", kFormat)) << kFormat;
  }
  EXPECT_FALSE(RefusedByName("top.ia", vpiIntVal));
}

TEST_F(ArrayRefusalsOfARun, DISABLED_ARealElementIsRefusedEveryBitFormat) {
  Run("module top; real r[2]; shortreal s[2]; initial $noop; endmodule\n");
  for (const char* name : {"top.r", "top.s"}) {
    for (const PLI_UINT32 kFormat :
         {vpiRawFourStateVal, vpiRawTwoStateVal, vpiVectorVal}) {
      EXPECT_TRUE(RefusedByName(name, kFormat)) << name << " " << kFormat;
    }
  }
}

TEST_F(ArrayRefusalsOfARun, ARealElementIsRefusedTheShortRealFormat) {
  Run("module top; real r[2]; shortreal s[2]; initial $noop; endmodule\n");
  EXPECT_TRUE(RefusedByName("top.r", vpiShortRealVal));
  EXPECT_FALSE(RefusedByName("top.s", vpiShortRealVal));
  EXPECT_FALSE(RefusedByName("top.r", vpiRealVal));
}

TEST_F(ArrayRefusalsOfARun, TheLongFormatIsRefusedOutsideItsThreeKinds) {
  Run("module top;\n"
      "  typedef enum {A, B} e_t;\n"
      "  int i[2]; bit [7:0] b[2]; integer g[2]; time t[2]; real r[2];\n"
      "  e_t e[2]; longint l[2];\n"
      "  initial $noop;\n"
      "endmodule\n");
  for (const char* name :
       {"top.i", "top.b", "top.g", "top.t", "top.r", "top.e"}) {
    EXPECT_TRUE(RefusedByName(name, vpiLongIntVal)) << name;
  }
  EXPECT_FALSE(RefusedByName("top.l", vpiLongIntVal));
}

TEST_F(ArrayRefusalsOfARun, TheShortFormatIsRefusedOutsideItsTwoKinds) {
  Run("module top;\n"
      "  int i[2]; longint l[2]; bit [7:0] b[2]; shortint h[2];\n"
      "  initial $noop;\n"
      "endmodule\n");
  for (const char* name : {"top.i", "top.l", "top.b"}) {
    EXPECT_TRUE(RefusedByName(name, vpiShortIntVal)) << name;
  }
  EXPECT_FALSE(RefusedByName("top.h", vpiShortIntVal));
}

TEST_F(ArrayRefusalsOfARun, DISABLED_AnElementOfUnpackedTypeIsRefused) {
  Run("module top;\n"
      "  typedef struct { int x; } s_t; s_t s[4];\n"
      "  typedef union { int x; bit [31:0] y; } u_t; u_t u[4];\n"
      "  initial $noop;\n"
      "endmodule\n");
  EXPECT_TRUE(RefusedByName("top.s", vpiIntVal));
  EXPECT_TRUE(RefusedByName("top.u", vpiIntVal));
}

TEST_F(ArrayRefusalsOfARun, AnAssociativeArrayOrQueueIsRefused) {
  Run("module top;\n"
      "  int aa[int]; int qq[$];\n"
      "  initial begin aa[0] = 1; qq.push_back(2); end\n"
      "endmodule\n");
  EXPECT_TRUE(RefusedByName("top.aa", vpiIntVal));
  EXPECT_TRUE(RefusedByName("top.qq", vpiIntVal));
}

TEST_F(ArrayRefusalsOfARun, AnArrayOfDynamicArraysIsRefused) {
  Run("module top;\n"
      "  int da[2][]; int dq[2][$]; int ds[2][string];\n"
      "  initial $noop;\n"
      "endmodule\n");
  for (const char* name : {"top.da", "top.dq", "top.ds"}) {
    EXPECT_TRUE(Refused(By(name), vpiIntVal, {0, 0}, 1) &&
                Refused(By(name), vpiIntVal, {0}, 1))
        << name;
  }
}

TEST_F(ArrayRefusalsOfARun, DISABLED_AnArrayOfHandlesIsRefused) {
  Run("module top;\n"
      "  class C; endclass\n"
      "  C c[2]; chandle h[2];\n"
      "  initial $noop;\n"
      "endmodule\n");
  for (const char* name : {"top.c", "top.h"}) {
    EXPECT_TRUE(Refused(By(name), vpiIntVal, {0, 0}, 1) &&
                Refused(By(name), vpiIntVal, {0}, 1))
        << name;
  }
}

TEST_F(ArrayRefusalsOfARun, AnArrayOfAProgramIsRead) {
  Run("program prg; int ga[2] = '{21, 22}; initial #2; endprogram\n"
      "module top; prg g(); initial $noop; endmodule\n");
  EXPECT_EQ(FirstInt(By("top.g.ga")), 21);
}

TEST_F(ArrayRefusalsOfARun, DISABLED_AnArrayOfAPackageIsRead) {
  Run("package p; int pa[2] = '{11, 12}; endpackage\n"
      "module top; initial $noop; endmodule\n");
  EXPECT_EQ(FirstInt(By("p::pa")), 11);
}

std::map<std::string, bool>& Refusals() {
  static std::map<std::string, bool> refusals;
  return refusals;
}

PLI_INT32 ReadLocalCalltf(PLI_BYTE8*) {
  vpiHandle local = vpi_handle_by_name(VpiText("top.t.la"), nullptr);
  Refusals()["automatic"] =
      local != nullptr && Refused(local, vpiIntVal, {0}, 1);
  vpiHandle kept = vpi_handle_by_name(VpiText("top.t.sa"), nullptr);
  Refusals()["static"] = kept == nullptr || Refused(kept, vpiIntVal, {0}, 1);
  return 0;
}

TEST_F(ArrayRefusalsOfARun, DISABLED_AnArrayOfAutomaticLifetimeIsRefused) {
  Refusals().clear();
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$read_local");
  data.calltf = &ReadLocalCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
  Run("module top;\n"
      "  task automatic t;\n"
      "    int la[2]; static int sa[2];\n"
      "    la[0] = 3; sa[0] = 4; $read_local;\n"
      "  endtask\n"
      "  initial t;\n"
      "endmodule\n");
  EXPECT_EQ(Refusals(), (std::map<std::string, bool>{{"automatic", true},
                                                     {"static", false}}));
}

TEST_F(ArrayRefusalsOfARun, DISABLED_ANonStaticClassPropertyIsRefused) {
  Run("module top;\n"
      "  class C; int a[2]; static int sa[2] = '{5, 6}; endclass\n"
      "  C obj; initial begin obj = new; obj.a[0] = 7; end\n"
      "endmodule\n");
  EXPECT_TRUE(RefusedByName("top.obj.a", vpiIntVal));
  EXPECT_EQ(FirstInt(By("top.C::sa")), 5);
}

}  // namespace
}  // namespace delta
