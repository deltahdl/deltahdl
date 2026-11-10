#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kInterfaceWithAType =
    "interface ifc; typedef logic [5:0] w6_t; endinterface\n"
    "class K #(type T = int); T v; endclass\n"
    "module c #(parameter type T = int) (); T v; endmodule\n"
    "interface j #(parameter type T = int); endinterface\n";

struct HierarchicalTypeValue {
  std::string_view item;
  std::string_view report;
  std::string_view subclause;
};

constexpr std::string_view kNotAType = "does not name a type";
constexpr std::string_view kNotADataType = "can only be set to a data type";

constexpr HierarchicalTypeValue kHierarchicalTypeValues[] = {
    {"module t; ifc i(); c #(.T(i.w6_t)) u(); endmodule\n", kNotAType,
     "23.10.2"},
    {"module t; ifc i(); c #(i.w6_t) u(); endmodule\n", kNotAType, "23.10.2"},
    {"module t; ifc i(); j #(i.w6_t) jj(); endmodule\n", kNotAType, "23.10.2"},
    {"module t; ifc i(); K #(i.w6_t) k; endmodule\n",
     "parameter override is not a constant expression", "23.10.2"},
    {"module t; ifc i(); localparam type L = i.w6_t; endmodule\n",
     kNotADataType, "6.20.3"},
    {"module t; ifc i(); parameter type P = i.w6_t; endmodule\n", kNotADataType,
     "6.20.3"},
    {("module t; ifc i();\n"
      "  if (1) begin : g localparam type L = i.w6_t; end\n"
      "endmodule\n"),
     kNotADataType, "6.20.3"},
};

TEST(TypeParameterElab, HierarchicalNameAsATypeParameterValueIsReported) {
  for (const auto& value : kHierarchicalTypeValues) {
    std::string src =
        std::string(kInterfaceWithAType) + std::string(value.item);
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), std::string(value.report),
                              LineHolding(src, "i.w6_t"),
                              std::string(value.subclause)));
  }
}

TEST(TypeParameterElab, LocalTypeAsATypeParameterValueIsAccepted) {
  for (const auto& value : kHierarchicalTypeValues) {
    std::string src =
        std::string(kInterfaceWithAType) + std::string(value.item);
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
