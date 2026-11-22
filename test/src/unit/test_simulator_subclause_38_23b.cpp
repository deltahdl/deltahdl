#include <gtest/gtest.h>

#include <set>
#include <string>
#include <string_view>
#include <vector>

#include "fixture_vpi_run.h"
#include "helpers_sealed_design_run.h"
#include "preprocessor/protect_processing.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

constexpr const char* kMixed =
    "module m; wire w0, w1; logic r0, r1, r2; endmodule\n"
    "module top; m m1(); initial $noop; endmodule\n";

class IterationOfARun : public VpiDesignRun {
 protected:
  static std::set<std::string> NameSetOf(int type, vpiHandle ref) {
    const std::vector<std::string> kNames = NamesOf(type, ref);
    return {kNames.begin(), kNames.end()};
  }
};

TEST_F(IterationOfARun, TheIteratorOfARunIsOfTypeIterator) {
  Run(kMixed);
  vpiHandle iter = vpi_iterate(vpiNet, By("top.m1"));
  ASSERT_NE(iter, nullptr);
  EXPECT_EQ(vpi_get(vpiType, iter), vpiIterator);
}

TEST_F(IterationOfARun, TheIteratorLeadsBackToItsReference) {
  Run(kMixed);
  vpiHandle mod = By("top.m1");
  vpiHandle iter = vpi_iterate(vpiNet, mod);
  ASSERT_NE(iter, nullptr);
  vpiHandle use = vpi_handle(vpiUse, iter);
  ASSERT_NE(use, nullptr);
  EXPECT_NE(vpi_compare_objects(use, mod), 0);
}

TEST_F(IterationOfARun, OnlyObjectsOfTheAskedTypeAreWalked) {
  Run(kMixed);
  vpiHandle mod = By("top.m1");
  EXPECT_EQ(NameSetOf(vpiNet, mod), (std::set<std::string>{"w0", "w1"}));
  EXPECT_EQ(NameSetOf(vpiReg, mod), (std::set<std::string>{"r0", "r1", "r2"}));
}

TEST_F(IterationOfARun, NoObjectOfTheAskedTypeGivesNoIterator) {
  Run("module m; logic r0; endmodule\n"
      "module top; m m1(); initial $noop; endmodule\n");
  vpiHandle mod = By("top.m1");
  ASSERT_NE(mod, nullptr);
  EXPECT_EQ(vpi_iterate(vpiNet, mod), nullptr);
  EXPECT_NE(vpi_iterate(vpiReg, mod), nullptr);
}

constexpr std::string_view kKey = "iteration-key";

class IterationOfASealedRun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    RunUnderKey(EncryptEnvelopes("`pragma protect begin\n"
                                 "module secret; logic r0, r1; endmodule\n"
                                 "`pragma protect end\n"
                                 "module t; logic p0; secret u();\n"
                                 "  initial $noop; endmodule\n",
                                 kKey),
                kKey, f_);
  }

  static PLI_INT32 ErrorLevel() {
    s_vpi_error_info info = {};
    return vpi_chk_error(&info);
  }
};

TEST_F(IterationOfASealedRun, IteratingAProtectedInstanceIsAnError) {
  vpiHandle sealed = By("t.u");
  ASSERT_NE(sealed, nullptr);
  EXPECT_EQ(vpi_iterate(vpiReg, sealed), nullptr);
  const PLI_INT32 kLevel = ErrorLevel();
  EXPECT_EQ(kLevel, vpiError);
}

TEST_F(IterationOfASealedRun, IteratingTheInstanceAroundItIsNoError) {
  vpiHandle top = By("t");
  ASSERT_NE(top, nullptr);
  EXPECT_NE(vpi_iterate(vpiReg, top), nullptr);
  const PLI_INT32 kLevel = ErrorLevel();
  EXPECT_EQ(kLevel, 0);
}

}  // namespace
}  // namespace delta
