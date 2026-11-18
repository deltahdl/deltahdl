#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string ExportedThroughTarget(const std::string& definition) {
  return "interface sb(input logic clk);\n"
         "  modport target(input clk, export Read);\n"
         "  modport initiator(input clk,\n"
         "    import task Read(input logic [7:0] raddr));\n"
         "endinterface\n"
         "module memMod(interface a);\n"
         "  " +
         definition +
         "\n"
         "endmodule\n"
         "module cpuMod(interface b);\n"
         "  initial b.Read(8'h1);\n"
         "endmodule\n"
         "module top;\n"
         "  logic clk;\n"
         "  sb s(clk);\n"
         "  memMod mem(s.target);\n"
         "  cpuMod cpu(s.initiator);\n"
         "endmodule\n";
}

void ExpectImportRefused(const std::string& definition) {
  ElabFixture f;
  ElaborateSrc(ExportedThroughTarget(definition), f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the prototype of 'Read' modport 'initiator' "
                            "imports does not match its definition in module "
                            "'memMod'",
                            4, "25.7"));
}

TEST(ImportOfAnExportedTask, ADefinitionMatchingTheImportPrototypeIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      ExportedThroughTarget("task a.Read(input logic [7:0] raddr); endtask"), f,
      "top");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ImportOfAnExportedTask, DISABLED_ADefinitionWithoutTheArgumentIsRefused) {
  ExpectImportRefused("task a.Read; endtask");
}

TEST(ImportOfAnExportedTask, DISABLED_ADefinitionWithAnExtraArgumentIsRefused) {
  ExpectImportRefused(
      "task a.Read(input logic [7:0] raddr, input bit x); endtask");
}

TEST(ImportOfAnExportedTask, DISABLED_ADefinitionOfAnotherTypeIsRefused) {
  ExpectImportRefused("task a.Read(input string raddr); endtask");
}

TEST(ImportOfAnExportedTask, DISABLED_ADefinitionOfAnotherDirectionIsRefused) {
  ExpectImportRefused("task a.Read(output logic [7:0] raddr); endtask");
}

TEST(ImportOfAnExportedTask, DISABLED_ADefinitionRenamingTheFormalIsRefused) {
  ExpectImportRefused("task a.Read(input logic [7:0] other); endtask");
}

TEST(ImportOfAnExportedTask, DISABLED_AFunctionDefinitionIsRefused) {
  ExpectImportRefused(
      "function void a.Read(input logic [7:0] raddr); endfunction");
}

}  // namespace
