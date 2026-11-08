#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(UserDefinedTypeElaboration, AModuleTypedefNamesTheOuterTypeOfItsName) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; task t(); endtask endinterface\n"
      "class H; virtual ifc vif; endclass\n"
      "typedef H HU;\n"
      "module top;\n"
      "  typedef HU HU;\n"
      "  HU h = new;\n"
      "  initial if (0) h.vif.t();\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UserDefinedTypeElaboration,
     AModuleTypedefOfTheOuterNameReachesTheOuterTypesMembers) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; task t(); endtask endinterface\n"
      "class H; virtual ifc vif; endclass\n"
      "typedef H HU;\n"
      "module top;\n"
      "  typedef HU HU;\n"
      "  HU h = new;\n"
      "  initial if (0) h.vif.nosuch();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'nosuch' names no task or function of interface 'ifc'", 7, "25.9"));
}

TEST(UserDefinedTypeElaboration, AModuleTypedefNamesTheOuterClassOfItsName) {
  ElabFixture f;
  ElaborateSrc(
      "class HU; int x; endclass\n"
      "module top;\n"
      "  typedef HU HU;\n"
      "  HU h = new;\n"
      "  initial h.x = 1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

uint32_t VarWidth(const std::string& src, std::string_view name) {
  ElabFixture f;
  auto* design = ElaborateSrc(src, f);
  if (design == nullptr || f.diag.HasErrors()) return 0;
  for (const auto& var : design->top_modules[0]->variables) {
    if (var.name == name) return var.width;
  }
  return 0;
}

TEST(UserDefinedTypeElaboration, AModuleTypedefOfTheOuterVectorKeepsItsWidth) {
  EXPECT_EQ(VarWidth("typedef logic [11:0] w_t;\n"
                     "module top;\n"
                     "  typedef w_t w_t;\n"
                     "  w_t v;\n"
                     "endmodule\n",
                     "v"),
            12u);
}

TEST(UserDefinedTypeElaboration,
     AModuleTypedefOfTheOuterVectorWithPackedDimensionsPacksIt) {
  EXPECT_EQ(VarWidth("typedef logic [3:0] w_t;\n"
                     "module top;\n"
                     "  typedef w_t [1:0] w_t;\n"
                     "  w_t v;\n"
                     "endmodule\n",
                     "v"),
            8u);
}

TEST(UserDefinedTypeElaboration,
     AModuleTypedefOfAnOuterNameWithPackedDimensionsPacksWhatItNames) {
  EXPECT_EQ(VarWidth("typedef logic [3:0] nib_t;\n"
                     "typedef nib_t w_t;\n"
                     "module top;\n"
                     "  typedef w_t [2:0] w_t;\n"
                     "  w_t v;\n"
                     "endmodule\n",
                     "v"),
            12u);
}

}  // namespace
