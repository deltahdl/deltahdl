#include <gtest/gtest.h>

#include <utility>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class PropertiesOfARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    Run("module top; int v;\n"
        "  function int f; return 0; endfunction\n"
        "  initial $noop;\n"
        "endmodule\n");
  }

  static void ExpectUndefinedWithAnError(int prop, vpiHandle obj,
                                         const char* label) {
    EXPECT_EQ(vpi_get(prop, obj), vpiUndefined) << label;
    const PLI_INT32 kLevel = vpi_chk_error(nullptr);
    EXPECT_NE(kLevel, 0) << label;
    EXPECT_EQ(vpi_get64(prop, obj), vpiUndefined) << label;
    const PLI_INT32 kLevel64 = vpi_chk_error(nullptr);
    EXPECT_NE(kLevel64, 0) << label;
  }
};

TEST_F(PropertiesOfARun, APropertyAFunctionHasIsAnswered) {
  vpiHandle f = Named(vpiFunction, By("top"), "f");
  ASSERT_NE(f, nullptr);
  EXPECT_NE(vpi_get(vpiFuncType, f), vpiUndefined);
  const PLI_INT32 kLevel = vpi_chk_error(nullptr);
  EXPECT_EQ(kLevel, 0);
}

TEST_F(PropertiesOfARun, DISABLED_APropertyNotDrawnOnTheKindIsUndefined) {
  vpiHandle top = By("top");
  vpiHandle v = By("top.v");
  ASSERT_NE(top, nullptr);
  ASSERT_NE(v, nullptr);
  const std::vector<std::pair<const char*, int>> kProps = {
      {"vpiDelayType", vpiDelayType}, {"vpiFuncType", vpiFuncType},
      {"vpiUserDefn", vpiUserDefn},   {"vpiDistType", vpiDistType},
      {"vpiTagged", vpiTagged},       {"vpiSoft", vpiSoft},
      {"vpiPacked", vpiPacked},
  };
  for (const auto& [name, prop] : kProps) {
    EXPECT_EQ(vpi_get(prop, top), vpiUndefined) << name << " of a module";
  }
  EXPECT_EQ(vpi_get(vpiFuncType, v), vpiUndefined) << "vpiFuncType of an int";
  EXPECT_EQ(vpi_get(vpiDistType, v), vpiUndefined) << "vpiDistType of an int";
}

TEST_F(PropertiesOfARun, DISABLED_ACodeNamingNoPropertyIsAnError) {
  ExpectUndefinedWithAnError(987654, By("top"), "unknown code");
}

TEST_F(PropertiesOfARun, DISABLED_AStringPropertyIsAnError) {
  ExpectUndefinedWithAnError(vpiName, By("top"), "vpiName");
  ExpectUndefinedWithAnError(vpiFullName, By("top.v"), "vpiFullName");
}

}  // namespace
}  // namespace delta
