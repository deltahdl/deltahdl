#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

constexpr std::string_view kInterfaceWithAType =
    "interface ifc; typedef logic [5:0] w6_t; endinterface\n"
    "class K #(type T = int); T v; endclass\n"
    "module c #(parameter type T = int) (); T v; endmodule\n"
    "interface j #(parameter type T = int); endinterface\n";

constexpr std::string_view kHierarchicalTypeValues[] = {
    "module t; ifc i(); c #(.T(i.w6_t)) u(); endmodule\n",
    "module t; ifc i(); c #(i.w6_t) u(); endmodule\n",
    "module t; ifc i(); j #(i.w6_t) jj(); endmodule\n",
    "module t; ifc i(); K #(i.w6_t) k; endmodule\n",
    "module t; ifc i(); localparam type L = i.w6_t; endmodule\n",
    "module t; ifc i(); parameter type P = i.w6_t; endmodule\n",
    ("module t; ifc i();\n"
     "  if (1) begin : g localparam type L = i.w6_t; end\n"
     "endmodule\n"),
};

TEST(TypeParameterElab, HierarchicalNameAsATypeParameterValueIsReported) {
  for (std::string_view item : kHierarchicalTypeValues) {
    std::string src = std::string(kInterfaceWithAType) + std::string(item);
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_TRUE(f.diag.HasErrors());
  }
}

TEST(TypeParameterElab, LocalTypeAsATypeParameterValueIsAccepted) {
  for (std::string_view item : kHierarchicalTypeValues) {
    std::string src = std::string(kInterfaceWithAType) + std::string(item);
    for (auto pos = src.find("i.w6_t"); pos != std::string::npos;
         pos = src.find("i.w6_t")) {
      src.replace(pos, 6, "w6_t");
    }
    src.replace(src.find("module t"), 8, "typedef logic [5:0] w6_t;\nmodule t");
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_FALSE(f.diag.HasErrors());
  }
}

}  // namespace
