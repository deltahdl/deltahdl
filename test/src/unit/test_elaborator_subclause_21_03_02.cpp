#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const std::vector<std::string>& FileOutputTaskNames() {
  static const std::vector<std::string> kNames = {
      "$fdisplay", "$fdisplayb", "$fdisplayh", "$fdisplayo",
      "$fwrite",   "$fwriteb",   "$fwriteh",   "$fwriteo",
      "$fstrobe",  "$fstrobeb",  "$fstrobeh",  "$fstrobeo",
      "$fmonitor", "$fmonitorb", "$fmonitorh", "$fmonitoro"};
  return kNames;
}

constexpr const char* kNotADescriptor =
    "the first argument of a file output task must be a multichannel "
    "descriptor or a file descriptor";

std::string CallInModule(const std::string& decl, const std::string& call) {
  return "module t;\n" + decl + "\n  initial " + call + ";\nendmodule\n";
}

void ExpectReported(const std::string& src, uint32_t line) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(src, f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotADescriptor, line, "21.3.2"))
      << src;
}

void ExpectAccepted(const std::string& src) {
  ElabFixture f;
  Elaborate(src, f);
  EXPECT_FALSE(f.has_errors) << src;
}

TEST(FileOutputTaskDescriptor, DISABLED_EmptyParenthesesAreReported) {
  for (const auto& name : FileOutputTaskNames()) {
    ExpectReported(CallInModule("  int x;", name + "()"), 3);
  }
}

TEST(FileOutputTaskDescriptor, DISABLED_ACallWithNoParenthesesIsReported) {
  for (const auto& name : FileOutputTaskNames()) {
    ExpectReported(CallInModule("  int x;", name), 3);
  }
}

TEST(FileOutputTaskDescriptor, DISABLED_ARealDescriptorIsReported) {
  for (const auto& name : FileOutputTaskNames()) {
    ExpectReported(CallInModule("  real d;", name + "(d, \"x\")"), 3);
  }
}

TEST(FileOutputTaskDescriptor, DISABLED_AShortrealDescriptorIsReported) {
  ExpectReported(CallInModule("  shortreal d;", "$fdisplay(d, \"x\")"), 3);
}

TEST(FileOutputTaskDescriptor, DISABLED_ARealtimeDescriptorIsReported) {
  ExpectReported(CallInModule("  realtime d;", "$fwrite(d, \"x\")"), 3);
}

TEST(FileOutputTaskDescriptor, DISABLED_ARealLiteralDescriptorIsReported) {
  ExpectReported(CallInModule("  int x;", "$fdisplay(1.5, \"x\")"), 3);
}

TEST(FileOutputTaskDescriptor, DISABLED_AStringDescriptorIsReported) {
  for (const auto& name : FileOutputTaskNames()) {
    ExpectReported(CallInModule("  string d;", name + "(d, \"x\")"), 3);
  }
}

TEST(FileOutputTaskDescriptor, DISABLED_AnUnpackedArrayDescriptorIsReported) {
  ExpectReported(CallInModule("  int d[2];", "$fstrobe(d, \"x\")"), 3);
}

TEST(FileOutputTaskDescriptor, DISABLED_AClassHandleDescriptorIsReported) {
  ExpectReported(
      "class C; endclass\n"
      "module t;\n"
      "  C d;\n"
      "  initial $fmonitor(d, \"x\");\n"
      "endmodule\n",
      4);
}

TEST(FileOutputTaskDescriptor, DISABLED_AChandleDescriptorIsReported) {
  ExpectReported(CallInModule("  chandle d;", "$fdisplay(d, \"x\")"), 3);
}

TEST(FileOutputTaskDescriptor, DISABLED_ARealDescriptorInAFunctionIsReported) {
  ExpectReported(
      "module t;\n"
      "  function void put(real d);\n"
      "    $fdisplay(d, \"x\");\n"
      "  endfunction\n"
      "endmodule\n",
      3);
}

TEST(FileOutputTaskDescriptor,
     DISABLED_AStringDescriptorInAClassMethodIsReported) {
  ExpectReported(
      "class C;\n"
      "  string d;\n"
      "  task put();\n"
      "    $fwrite(d, \"x\");\n"
      "  endtask\n"
      "endclass\n",
      4);
}

TEST(FileOutputTaskDescriptor,
     DISABLED_ARealDescriptorInAnInterfaceOrProgramIsReported) {
  ExpectReported(
      "interface i;\n"
      "  real d;\n"
      "  initial $fstrobe(d, \"x\");\n"
      "endinterface\n",
      3);
  ExpectReported(
      "program p;\n"
      "  real d;\n"
      "  initial $fmonitor(d, \"x\");\n"
      "endprogram\n",
      3);
}

TEST(FileOutputTaskDescriptor, EveryTaskAcceptsAnIntegerDescriptor) {
  for (const auto& name : FileOutputTaskNames()) {
    ExpectAccepted(CallInModule("  integer d;", name + "(d, \"x\")"));
    ExpectAccepted(CallInModule("  integer d;", name + "(d)"));
  }
}

TEST(FileOutputTaskDescriptor, EveryIntegralKindOfDescriptorIsAccepted) {
  ExpectAccepted(
      "module t;\n"
      "  int a;\n"
      "  int unsigned b;\n"
      "  logic [31:0] c;\n"
      "  bit [31:0] e;\n"
      "  initial begin\n"
      "    $fdisplay(a, \"x\");\n"
      "    $fwrite(b, \"x\");\n"
      "    $fstrobe(c, \"x\");\n"
      "    $fmonitor(e, \"x\");\n"
      "    $fdisplay(a | b, \"x\");\n"
      "    $fdisplay(1, \"x\");\n"
      "    $fdisplay(32'h8000_0002, \"x\");\n"
      "  end\n"
      "endmodule\n");
}

TEST(FileOutputTaskDescriptor, AnIntegralDescriptorIsAcceptedInEveryPlace) {
  ExpectAccepted(
      "interface i;\n"
      "  integer d;\n"
      "  initial $fstrobe(d, \"x\");\n"
      "endinterface\n"
      "program p;\n"
      "  integer d;\n"
      "  initial $fmonitor(d, \"x\");\n"
      "endprogram\n"
      "package k;\n"
      "  function void put(integer d); $fdisplay(d, \"x\"); endfunction\n"
      "endpackage\n"
      "class C;\n"
      "  integer d;\n"
      "  task put(); $fwrite(d, \"x\"); endtask\n"
      "endclass\n"
      "module t;\n"
      "  integer d;\n"
      "  function void put(); $fdisplayh(d, 1); endfunction\n"
      "  task tput(); $fwriteb(d, 1); endtask\n"
      "  for (genvar g = 0; g < 2; g++) begin : gen\n"
      "    initial $fdisplayo(d, g);\n"
      "  end\n"
      "endmodule\n");
}

}  // namespace
