#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kABus =
    "interface A_Bus(input logic clk);\n"
    "  wire req, gnt;\n"
    "  wire [7:0] addr, data;\n"
    "  clocking sb @(posedge clk);\n"
    "    input gnt;\n"
    "    output req, addr;\n"
    "    inout data;\n"
    "    property p1; req ##[1:3] gnt; endproperty\n"
    "  endclocking\n"
    "  modport DUT(input clk, req, addr, output gnt, inout data);\n"
    "  modport STB(clocking sb);\n"
    "  modport TB(input gnt, output req, addr, inout data);\n"
    "endinterface\n";

std::string ThroughAVirtualInterface(const std::string& type,
                                     const std::string& stmt) {
  return std::string(kABus) +
         "module top;\n"
         "  logic clk = 0;\n"
         "  A_Bus b1(clk);\n"
         "  " +
         type +
         " v = b1;\n"
         "  initial begin\n"
         "    " +
         stmt +
         "\n"
         "  end\n"
         "endmodule\n";
}

std::string ThroughAPort(const std::string& type, const std::string& stmt) {
  return std::string(kABus) + "program T(" + type +
         " b);\n"
         "  initial begin\n"
         "    " +
         stmt +
         "\n"
         "  end\n"
         "endprogram\n"
         "module top;\n"
         "  logic clk = 0;\n"
         "  A_Bus b1(clk);\n"
         "  T t(b1);\n"
         "endmodule\n";
}

std::string ThroughATypedefFormal(const std::string& stmt) {
  return std::string(kABus) +
         "program T(A_Bus.STB b1);\n"
         "  typedef virtual A_Bus.STB SYNCTB;\n"
         "  task drive(SYNCTB s, logic [7:0] adr);\n"
         "    " +
         stmt +
         "\n"
         "  endtask\n"
         "  initial drive(b1, 8'h12);\n"
         "endprogram\n"
         "module top;\n"
         "  logic clk = 0;\n"
         "  A_Bus b1(clk);\n"
         "  T t(b1);\n"
         "endmodule\n";
}

void ExpectAccepted(const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f, "top");
  EXPECT_FALSE(f.diag.HasErrors());
}

void ExpectBlockRefused(const std::string& src, const std::string& modport,
                        int line) {
  ElabFixture f;
  ElaborateSrc(src, f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "clocking block 'sb' is not accessible through "
                            "modport '" +
                                modport + "' of interface 'A_Bus'",
                            line, "25.5.5"));
}

void ExpectBlockingWriteRefused(const std::string& src, int line) {
  ElabFixture f;
  ElaborateSrc(src, f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a clockvar is written only by a synchronous drive "
                            "(<=), not by a blocking assignment",
                            line, "14.16"));
}

TEST(VirtualInterfaceModportClocking,
     AVirtualInterfaceWithoutAModportDrivesTheBlock) {
  ExpectAccepted(ThroughAVirtualInterface("virtual A_Bus", "v.sb.req <= 1;"));
}

TEST(VirtualInterfaceModportClocking,
     AVirtualInterfaceOfTheClockingModportDrivesTheBlock) {
  ExpectAccepted(
      ThroughAVirtualInterface("virtual A_Bus.STB", "v.sb.req <= 1;"));
}

TEST(VirtualInterfaceModportClocking,
     AVirtualInterfaceOfTheClockingModportWaitsOnTheBlock) {
  ExpectAccepted(ThroughAVirtualInterface("virtual A_Bus.STB", "@(v.sb);"));
}

TEST(VirtualInterfaceModportClocking,
     AVirtualInterfaceOfAModportWithoutTheBlockCannotDriveIt) {
  ExpectBlockRefused(
      ThroughAVirtualInterface("virtual A_Bus.TB", "v.sb.req <= 1;"), "TB", 19);
}

TEST(VirtualInterfaceModportClocking,
     AVirtualInterfaceOfAModportWithoutTheBlockCannotReadIt) {
  ExpectBlockRefused(
      ThroughAVirtualInterface("virtual A_Bus.DUT", "wait (v.sb.gnt == 1);"),
      "DUT", 19);
}

TEST(VirtualInterfaceModportClocking,
     DISABLED_AVirtualInterfaceOfAModportWithoutTheBlockCannotWaitOnIt) {
  ExpectBlockRefused(ThroughAVirtualInterface("virtual A_Bus.DUT", "@(v.sb);"),
                     "DUT", 19);
}

TEST(VirtualInterfaceModportClocking,
     APortOfTheClockingModportWaitsOnTheBlock) {
  ExpectAccepted(ThroughAPort("A_Bus.STB", "@(b.sb);"));
}

TEST(VirtualInterfaceModportClocking,
     APortOfAModportWithoutTheBlockCannotDriveIt) {
  ExpectBlockRefused(ThroughAPort("A_Bus.TB", "b.sb.req <= 1;"), "TB", 16);
}

TEST(VirtualInterfaceModportClocking,
     DISABLED_APortOfAModportWithoutTheBlockCannotWaitOnIt) {
  ExpectBlockRefused(ThroughAPort("A_Bus.DUT", "@(b.sb);"), "DUT", 16);
}

TEST(VirtualInterfaceModportClocking,
     ATypedefFormalDrivesAClockvarSynchronously) {
  ExpectAccepted(ThroughATypedefFormal("s.sb.addr <= adr;"));
}

TEST(VirtualInterfaceModportClocking,
     DISABLED_ATypedefFormalCannotWriteAClockvarByABlockingAssignment) {
  ExpectBlockingWriteRefused(ThroughATypedefFormal("s.sb.addr = adr;"), 17);
}

TEST(VirtualInterfaceModportClocking,
     DISABLED_AVirtualInterfaceCannotWriteAClockvarByABlockingAssignment) {
  ExpectBlockingWriteRefused(
      ThroughAVirtualInterface("virtual A_Bus.STB", "v.sb.req = 1;"), 19);
}

TEST(VirtualInterfaceModportClocking,
     DISABLED_APortCannotWriteAClockvarByABlockingAssignment) {
  ExpectBlockingWriteRefused(ThroughAPort("A_Bus.STB", "b.sb.req = 1;"), 16);
}

}  // namespace
