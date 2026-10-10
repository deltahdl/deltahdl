// §6.18 "User-defined types": a typedef names a type declared before it. The
// cases here declare a module's typedef under the name of a type the
// compilation unit declares, which §23.9 makes the type the name stands for
// until the module declares its own; packed dimensions written after the name
// pack that type (§7.4.1).

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// `typedef HU HU;` in a module names the compilation unit's HU, the class H,
// and declares the module's HU as that class (#5818). Recorded as written, HU
// named itself, and sizing h followed the name without end.
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

// The module's HU is the class H, so a call through h.vif is checked against
// the interface H's property refers to, and a task ifc lacks is reported.
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

// The outer name may be a class rather than a typedef, which leaves the table
// nothing to stand in for it: the module's HU is then the class HU itself.
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

// The width of the variable `name` the source's one module declares, or 0
// where it declares none.
uint32_t VarWidth(const std::string& src, std::string_view name) {
  ElabFixture f;
  auto* design = ElaborateSrc(src, f);
  if (design == nullptr || f.diag.HasErrors()) return 0;
  for (const auto& var : design->top_modules[0]->variables) {
    if (var.name == name) return var.width;
  }
  return 0;
}

// A typedef of a vector type under the name of the compilation unit's typedef
// is that vector, so a variable declared with the name has its width.
TEST(UserDefinedTypeElaboration, AModuleTypedefOfTheOuterVectorKeepsItsWidth) {
  EXPECT_EQ(VarWidth("typedef logic [11:0] w_t;\n"
                     "module top;\n"
                     "  typedef w_t w_t;\n"
                     "  w_t v;\n"
                     "endmodule\n",
                     "v"),
            12u);
}

// Packed dimensions written after the name pack the outer type's own (#5982):
// two of the outer four-bit vector are eight bits.
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

// The outer typedef may itself name a type, nib_t, with no dimensions of its
// own; three of it are twelve bits.
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
