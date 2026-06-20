#include "fixture_elaborator.h"

namespace {

TEST(PackageItemsElaboration, TypedefInPackageElaborates) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  typedef logic [7:0] byte_t;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "  byte_t x;\n"
             "endmodule\n"));
}

TEST(PackageItemsElaboration, FunctionInPackageElaborates) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  function int add(int a, int b); return a + b; endfunction\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "endmodule\n"));
}

TEST(PackageItemsElaboration, ParameterInPackageElaborates) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  parameter int WIDTH = 8;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "endmodule\n"));
}

TEST(PackageItemsElaboration, LocalparamInPackageElaborates) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  localparam int MAX = 255;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "endmodule\n"));
}

TEST(PackageItemsElaboration, ClassInPackageElaborates) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  class Pkt;\n"
             "    int data;\n"
             "  endclass\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "endmodule\n"));
}

TEST(PackageItemsElaboration, TaskInPackageElaborates) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  task do_work(); endtask\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "endmodule\n"));
}

TEST(PackageItemsElaboration, MixedItemsInPackageElaborate) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  typedef logic [7:0] byte_t;\n"
             "  parameter int WIDTH = 8;\n"
             "  function int add(int a, int b); return a + b; endfunction\n"
             "  class C;\n"
             "    int x;\n"
             "  endclass\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "  byte_t data;\n"
             "endmodule\n"));
}

TEST(PackageItemsElaboration, DataDeclInPackageElaborates) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  int shared_val = 42;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "endmodule\n"));
}

TEST(PackageItemsElaboration, MultiplePackagesWithImportsElaborate) {
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  typedef int t1;\n"
             "endpackage\n"
             "package p2;\n"
             "  typedef int t2;\n"
             "endpackage\n"
             "module m;\n"
             "  import p1::*;\n"
             "  import p2::*;\n"
             "endmodule\n"));
}

}  // namespace
