#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const char* const kNotInThisType =
    "random qualifier is only allowed in unpacked structures";

std::string ModuleImportingTakerOf(const std::string& type) {
  return "module m;\n"
         "  typedef " +
         type +
         " t_t;\n"
         "  import \"DPI-C\" function void c_take(input t_t v);\n"
         "endmodule\n";
}

bool Reports(const std::string& type) {
  ElabFixture f;
  Elaborate(ModuleImportingTakerOf(type), f, "m");
  return ReportedError(f.diag.Diagnostics(), kNotInThisType, 2, "7.2");
}

bool ElaboratesCleanly(const std::string& type) {
  ElabFixture f;
  Elaborate(ModuleImportingTakerOf(type), f, "m");
  return f.diag.Diagnostics().empty();
}

TEST(DpiRandomMembers, AUnionFormalWithThemIsRefused) {
  EXPECT_TRUE(Reports("union { rand int a; int b; }"));
  EXPECT_TRUE(Reports("union { int a; randc bit [1:0] b; }"));
}

TEST(DpiRandomMembers, APackedStructFormalWithThemIsRefused) {
  EXPECT_TRUE(Reports("struct packed { rand bit [7:0] a; bit b; }"));
  EXPECT_TRUE(Reports("struct packed { bit [7:0] a; randc bit b; }"));
}

TEST(DpiRandomMembers, AnUnpackedStructFormalWithThemIsAccepted) {
  EXPECT_TRUE(ElaboratesCleanly("struct { rand int a; randc bit [1:0] b; }"));
  EXPECT_TRUE(ElaboratesCleanly("struct packed { bit [7:0] a; bit b; }"));
}

}  // namespace
