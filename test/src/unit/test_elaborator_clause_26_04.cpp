#include "fixture_elaborator.h"

namespace {

TEST(PackageImportInHeader, TypedefVisibleInPortType) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  typedef logic [7:0] byte_t;\n"
             "endpackage\n"
             "module m import pkg::byte_t; (input byte_t a, output byte_t b);\n"
             "  assign b = a;\n"
             "endmodule\n"));
}

TEST(PackageImportInHeader, WildcardTypedefVisibleInPortType) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  typedef logic [15:0] word_t;\n"
             "endpackage\n"
             "module m import pkg::*; (input word_t a, output word_t b);\n"
             "  assign b = a;\n"
             "endmodule\n"));
}

TEST(PackageImportInHeader, ConstantVisibleInPortRange) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  parameter int W = 8;\n"
             "endpackage\n"
             "module m import pkg::W; (input [W-1:0] a, output [W-1:0] b);\n"
             "  assign b = a;\n"
             "endmodule\n"));
}

TEST(PackageImportInHeader, ConstantVisibleInParameterDefault) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  parameter int DEFAULT_W = 16;\n"
             "endpackage\n"
             "module m import pkg::DEFAULT_W; #(parameter int W = DEFAULT_W) "
             "(input [W-1:0] a);\n"
             "endmodule\n"));
}

TEST(PackageImportInHeader, WildcardImportVisibleInBody) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  typedef logic [3:0] nibble_t;\n"
             "endpackage\n"
             "module m import pkg::*; ();\n"
             "  nibble_t n;\n"
             "endmodule\n"));
}

TEST(PackageImportInHeader, ExplicitImportVisibleInBody) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  typedef logic signed [31:0] sword_t;\n"
             "endpackage\n"
             "module m import pkg::sword_t; ();\n"
             "  sword_t s;\n"
             "endmodule\n"));
}

TEST(PackageImportInHeader, MultipleHeaderImports) {
  EXPECT_TRUE(
      ElabOk("package a;\n"
             "  typedef logic [7:0] byte_t;\n"
             "endpackage\n"
             "package b;\n"
             "  parameter int N = 4;\n"
             "endpackage\n"
             "module m import a::byte_t, b::N; (input byte_t [N-1:0] data);\n"
             "endmodule\n"));
}

TEST(PackageImportInHeader, InterfaceHeaderImportVisibleInBody) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  typedef logic [7:0] byte_t;\n"
             "endpackage\n"
             "interface ifc import pkg::*; ();\n"
             "  byte_t data;\n"
             "endinterface\n"
             "module top;\n"
             "  ifc i();\n"
             "endmodule\n"));
}

}  // namespace
