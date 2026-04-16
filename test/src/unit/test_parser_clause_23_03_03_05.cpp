
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- R1: For an unpacked array port, the port and the array connected to the
//     port shall have the same number of unpacked dimensions, and each
//     dimension of the port shall have the same size as the corresponding
//     dimension of the array being connected ---

TEST(UnpackedArrayPortsAndArraysOfInstancesParser,
     InstanceArraySingleRangeDimensionParsed) {
  auto r = Parse("module m; child c[3:0](a, b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "child");
  EXPECT_EQ(item->inst_name, "c");
  ASSERT_EQ(item->inst_dims.size(), 1u);
  EXPECT_NE(item->inst_dims[0].first, nullptr);
  EXPECT_NE(item->inst_dims[0].second, nullptr);
  EXPECT_NE(item->inst_range_left, nullptr);
  EXPECT_NE(item->inst_range_right, nullptr);
}

TEST(UnpackedArrayPortsAndArraysOfInstancesParser,
     InstanceArraySingleSizeDimensionParsed) {
  auto r = Parse("module m; child c[4](a); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_dims.size(), 1u);
  EXPECT_NE(item->inst_dims[0].first, nullptr);
  EXPECT_EQ(item->inst_dims[0].second, nullptr);
  EXPECT_NE(item->inst_range_left, nullptr);
  EXPECT_EQ(item->inst_range_right, nullptr);
}

// --- R2/R3: Arrays of instances with port connections ---

TEST(UnpackedArrayPortsAndArraysOfInstancesParser,
     MultipleDimensionInstanceArrayParsed) {
  auto r = Parse("module m; child c[8][4](o, i); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_dims.size(), 2u);
  EXPECT_NE(item->inst_dims[0].first, nullptr);
  EXPECT_NE(item->inst_dims[1].first, nullptr);
}

TEST(UnpackedArrayPortsAndArraysOfInstancesParser,
     InstanceArrayWithNamedPortsParsed) {
  auto r = Parse("module m; child c[1:0](.a(x), .b(y)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_dims.size(), 1u);
  ASSERT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[0].first, "a");
  EXPECT_EQ(item->inst_ports[1].first, "b");
}

TEST(UnpackedArrayPortsAndArraysOfInstancesParser,
     InstanceArrayWithWildcardPortsParsed) {
  auto r = Parse("module m; child c[3:0](.*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_dims.size(), 1u);
  EXPECT_TRUE(item->inst_wildcard);
}

TEST(UnpackedArrayPortsAndArraysOfInstancesParser,
     InstanceArrayFirstDimCopiedToRangeFields) {
  auto r = Parse("module m; child c[7:0][3:0](a); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_dims.size(), 2u);
  EXPECT_EQ(item->inst_range_left, item->inst_dims[0].first);
  EXPECT_EQ(item->inst_range_right, item->inst_dims[0].second);
}

TEST(UnpackedArrayPortsAndArraysOfInstancesParser,
     InstanceArrayNoDimensionsLeavesFieldsEmpty) {
  auto r = Parse("module m; child c(a); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_dims.empty());
  EXPECT_EQ(item->inst_range_left, nullptr);
  EXPECT_EQ(item->inst_range_right, nullptr);
}

}  // namespace
