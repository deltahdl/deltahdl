#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(PackageItemsA111, NetDeclaration) {
  auto r = Parse(
      "package p;\n"
      "  wire w;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

TEST(PackageItemsA111, DataDeclaration) {
  auto r = Parse(
      "package p;\n"
      "  int x = 42;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsA111, TaskDeclaration) {
  auto r = Parse(
      "package p;\n"
      "  task do_work();\n"
      "  endtask\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsA111, FunctionDeclaration) {
  auto r = Parse(
      "package p;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->packages[0]->items, ModuleItemKind::kFunctionDecl));
}

TEST(PackageItemsA111, CheckerInPackage) {
  auto r = Parse(
      "package p;\n"
      "  checker my_chk;\n"
      "  endchecker\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsA111, DpiImport) {
  auto r = Parse(
      "package p;\n"
      "  import \"DPI-C\" function int c_func(int x);\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->packages[0]->items, ModuleItemKind::kDpiImport));
}

TEST(PackageItemsA111, ClassInPackage) {
  auto r = Parse(
      "package p;\n"
      "  class Pkt;\n"
      "    int data;\n"
      "  endclass\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsA111, InterfaceClassInPackage) {
  auto r = Parse(
      "package p;\n"
      "  interface class IFace;\n"
      "    pure virtual function void work();\n"
      "  endclass\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsA111, LocalparamInPackage) {
  auto r = Parse(
      "package p;\n"
      "  localparam int MAX = 255;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsA111, ParameterInPackage) {
  auto r = Parse(
      "package p;\n"
      "  parameter int WIDTH = 8;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsA111, CovergroupInPackage) {
  auto r = Parse(
      "package p;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsA111, PropertyInPackage) {
  auto r = Parse(
      "package p;\n"
      "  property prop_req;\n"
      "    @(posedge clk) req |-> ##[1:3] ack;\n"
      "  endproperty\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsA111, NullItem) {
  auto r = Parse(
      "package p;\n"
      "  ;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsA111, AnonymousProgram) {
  auto r = Parse(
      "package p;\n"
      "  program;\n"
      "    task run();\n"
      "    endtask\n"
      "  endprogram\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsA111, PackageExport) {
  auto r = Parse(
      "package p;\n"
      "  import other_pkg::*;\n"
      "  export other_pkg::*;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsA111, PackageTimeunits) {
  auto r = Parse(
      "package p;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsA111, PackageTypedef) {
  auto r = Parse(
      "package p;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsA111, PackageImport) {
  auto r = Parse(
      "package p;\n"
      "  import other_pkg::item;\n"
      "  import another_pkg::*;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsA111, ClassConstructorInPackage) {
  auto r = Parse(
      "package p;\n"
      "  class C;\n"
      "    function new(int val);\n"
      "    endfunction\n"
      "  endclass\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsA111, MixedPackageItems) {
  auto r = Parse(
      "package p;\n"
      "  parameter int W = 8;\n"
      "  typedef logic [W-1:0] data_t;\n"
      "  function data_t zero();\n"
      "    return '0;\n"
      "  endfunction\n"
      "  class Pkt;\n"
      "    data_t payload;\n"
      "  endclass\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_GE(r.cu->packages[0]->items.size(), 3u);
}

}  // namespace
